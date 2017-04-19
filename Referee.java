import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.io.StringReader;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Properties;
import java.util.Random;
import java.util.Scanner;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;

class Referee extends MultiReferee {
    private static final int LEAGUE_LEVEL = 3;

    private static final int MAP_WIDTH = 23;
    private static final int MAP_HEIGHT = 21;
    private static final int COOLDOWN_CANNON = 2;
    private static final int COOLDOWN_MINE = 5;
    private static final int INITIAL_SHIP_HEALTH = 100;
    private static final int MAX_SHIP_HEALTH = 100;
    private static final int MAX_SHIP_SPEED;
    private static final int MIN_SHIPS = 1;
    private static final int MAX_SHIPS;
    private static final int MIN_MINES;
    private static final int MAX_MINES;
    private static final int MIN_RUM_BARRELS = 10;
    private static final int MAX_RUM_BARRELS = 26;
    private static final int MIN_RUM_BARREL_VALUE = 10;
    private static final int MAX_RUM_BARREL_VALUE = 20;
    private static final int REWARD_RUM_BARREL_VALUE = 30;
    private static final int MINE_VISIBILITY_RANGE = 5;
    private static final int FIRE_DISTANCE_MAX = 10;
    private static final int LOW_DAMAGE = 25;
    private static final int HIGH_DAMAGE = 50;
    private static final int MINE_DAMAGE = 25;
    private static final int NEAR_MINE_DAMAGE = 10;
    private static final boolean CANNONS_ENABLED;
    private static final boolean MINES_ENABLED;

    static {
        switch (LEAGUE_LEVEL) {
        case 0: // 1 ship / no mines / speed 1
            MAX_SHIPS = 1;
            CANNONS_ENABLED = false;
            MINES_ENABLED = false;
            MIN_MINES = 0;
            MAX_MINES = 0;
            MAX_SHIP_SPEED = 1;
            break;
        case 1: // add mines
            MAX_SHIPS = 1;
            CANNONS_ENABLED = true;
            MINES_ENABLED = true;
            MIN_MINES = 5;
            MAX_MINES = 10;
            MAX_SHIP_SPEED = 1;
            break;
        case 2: // 3 ships max
            MAX_SHIPS = 3;
            CANNONS_ENABLED = true;
            MINES_ENABLED = true;
            MIN_MINES = 5;
            MAX_MINES = 10;
            MAX_SHIP_SPEED = 1;
            break;
        default: // increase max speed
            MAX_SHIPS = 3;
            CANNONS_ENABLED = true;
            MINES_ENABLED = true;
            MIN_MINES = 5;
            MAX_MINES = 10;
            MAX_SHIP_SPEED = 2;
            break;
        }
    }

    private static final Pattern PLAYER_INPUT_MOVE_PATTERN = Pattern.compile("MOVE (?<x>-?[0-9]{1,8})\\s+(?<y>-?[0-9]{1,8})(?:\\s+(?<message>.+))?",
            Pattern.CASE_INSENSITIVE);
    private static final Pattern PLAYER_INPUT_SLOWER_PATTERN = Pattern.compile("SLOWER(?:\\s+(?<message>.+))?", Pattern.CASE_INSENSITIVE);
    private static final Pattern PLAYER_INPUT_FASTER_PATTERN = Pattern.compile("FASTER(?:\\s+(?<message>.+))?", Pattern.CASE_INSENSITIVE);
    private static final Pattern PLAYER_INPUT_WAIT_PATTERN = Pattern.compile("WAIT(?:\\s+(?<message>.+))?", Pattern.CASE_INSENSITIVE);
    private static final Pattern PLAYER_INPUT_PORT_PATTERN = Pattern.compile("PORT(?:\\s+(?<message>.+))?", Pattern.CASE_INSENSITIVE);
    private static final Pattern PLAYER_INPUT_STARBOARD_PATTERN = Pattern.compile("STARBOARD(?:\\s+(?<message>.+))?", Pattern.CASE_INSENSITIVE);
    private static final Pattern PLAYER_INPUT_FIRE_PATTERN = Pattern.compile("FIRE (?<x>-?[0-9]{1,8})\\s+(?<y>-?[0-9]{1,8})(?:\\s+(?<message>.+))?",
            Pattern.CASE_INSENSITIVE);
    private static final Pattern PLAYER_INPUT_MINE_PATTERN = Pattern.compile("MINE(?:\\s+(?<message>.+))?", Pattern.CASE_INSENSITIVE);

    public static int clamp(int val, int min, int max) {
        return Math.max(min, Math.min(max, val));
    }

    public static long parseProperty(Properties prop, String key, long defaultValue) {
        try {
            return Long.valueOf(prop.getProperty(key));
        } catch (NumberFormatException e) {
            // Ignore invalid data
        }
        return defaultValue;
    }

    @SafeVarargs
    static final <T> String join(T... v) {
        return Stream.of(v).map(String::valueOf).collect(Collectors.joining(" "));
    }

    public static class Coord {
        private final static int[][] DIRECTIONS_EVEN = new int[][] { { 1, 0 }, { 0, -1 }, { -1, -1 }, { -1, 0 }, { -1, 1 }, { 0, 1 } };
        private final static int[][] DIRECTIONS_ODD = new int[][] { { 1, 0 }, { 1, -1 }, { 0, -1 }, { -1, 0 }, { 0, 1 }, { 1, 1 } };
        private final int x;
        private final int y;

        public Coord(int x, int y) {
            this.x = x;
            this.y = y;
        }

        public Coord(Coord other) {
            this.x = other.x;
            this.y = other.y;
        }

        public double angle(Coord targetPosition) {
            double dy = (targetPosition.y - this.y) * Math.sqrt(3) / 2;
            double dx = targetPosition.x - this.x + ((this.y - targetPosition.y) & 1) * 0.5;
            double angle = -Math.atan2(dy, dx) * 3 / Math.PI;
            if (angle < 0) {
                angle += 6;
            } else if (angle >= 6) {
                angle -= 6;
            }
            return angle;
        }

        CubeCoordinate toCubeCoordinate() {
            int xp = x - (y - (y & 1)) / 2;
            int zp = y;
            int yp = -(xp + zp);
            return new CubeCoordinate(xp, yp, zp);
        }

        Coord neighbor(int orientation) {
            int newY, newX;
            if (this.y % 2 == 1) {
                newY = this.y + DIRECTIONS_ODD[orientation][1];
                newX = this.x + DIRECTIONS_ODD[orientation][0];
            } else {
                newY = this.y + DIRECTIONS_EVEN[orientation][1];
                newX = this.x + DIRECTIONS_EVEN[orientation][0];
            }

            return new Coord(newX, newY);
        }

        boolean isInsideMap() {
            return x >= 0 && x < MAP_WIDTH && y >= 0 && y < MAP_HEIGHT;
        }

        int distanceTo(Coord dst) {
            return this.toCubeCoordinate().distanceTo(dst.toCubeCoordinate());
        }

        @Override
        public boolean equals(Object obj) {
            if (obj == null || getClass() != obj.getClass()) {
                return false;
            }
            Coord other = (Coord) obj;
            return y == other.y && x == other.x;
        }

        @Override
        public String toString() {
            return join(x, y);
        }
    }

    public static class CubeCoordinate {
        static int[][] directions = new int[][] { { 1, -1, 0 }, { +1, 0, -1 }, { 0, +1, -1 }, { -1, +1, 0 }, { -1, 0, +1 }, { 0, -1, +1 } };
        int x, y, z;

        public CubeCoordinate(int x, int y, int z) {
            this.x = x;
            this.y = y;
            this.z = z;
        }

        Coord toOffsetCoordinate() {
            int newX = x + (z - (z & 1)) / 2;
            int newY = z;
            return new Coord(newX, newY);
        }

        CubeCoordinate neighbor(int orientation) {
            int nx = this.x + directions[orientation][0];
            int ny = this.y + directions[orientation][1];
            int nz = this.z + directions[orientation][2];

            return new CubeCoordinate(nx, ny, nz);
        }

        int distanceTo(CubeCoordinate dst) {
            return (Math.abs(x - dst.x) + Math.abs(y - dst.y) + Math.abs(z - dst.z)) / 2;
        }

        @Override
        public String toString() {
            return join(x, y, z);
        }
    }

    private static enum EntityType {
        SHIP, BARREL, MINE, CANNONBALL
    }

    public static abstract class Entity {
        private static int UNIQUE_ENTITY_ID = 0;

        protected final int id;
        protected final EntityType type;
        protected Coord position;

        public Entity(EntityType type, int x, int y) {
            this.id = UNIQUE_ENTITY_ID++;
            this.type = type;
            this.position = new Coord(x, y);
        }

        public String toViewString() {
            return join(id, position.y, position.x);
        }

        protected String toPlayerString(int arg1, int arg2, int arg3, int arg4) {
            return join(id, type.name(), position.x, position.y, arg1, arg2, arg3, arg4);
        }
    }

    public static class Mine extends Entity {
        public Mine(int x, int y) {
            super(EntityType.MINE, x, y);
        }

        public String toPlayerString(int playerIdx) {
            return toPlayerString(0, 0, 0, 0);
        }

        public List<Damage> explode(List<Ship> ships, boolean force) {
            List<Damage> damage = new ArrayList<>();
            Ship victim = null;

            for (Ship ship : ships) {
                if (position.equals(ship.bow()) || position.equals(ship.stern()) || position.equals(ship.position)) {
                    damage.add(new Damage(this.position, MINE_DAMAGE, true));
                    ship.damage(MINE_DAMAGE);
                    victim = ship;
                }
            }

            if (force || victim != null) {
                if (victim == null) {
                    damage.add(new Damage(this.position, MINE_DAMAGE, true));
                }

                for (Ship ship : ships) {
                    if (ship != victim) {
                        Coord impactPosition = null;
                        if (ship.stern().distanceTo(position) <= 1) {
                            impactPosition = ship.stern();
                        }
                        if (ship.bow().distanceTo(position) <= 1) {
                            impactPosition = ship.bow();
                        }
                        if (ship.position.distanceTo(position) <= 1) {
                            impactPosition = ship.position;
                        }

                        if (impactPosition != null) {
                            ship.damage(NEAR_MINE_DAMAGE);
                            damage.add(new Damage(impactPosition, NEAR_MINE_DAMAGE, true));
                        }
                    }
                }
            }

            return damage;
        }
    }

    public static class Cannonball extends Entity {
        final int ownerEntityId;
        final int srcX;
        final int srcY;
        final int initialRemainingTurns;
        int remainingTurns;

        public Cannonball(int row, int col, int ownerEntityId, int srcX, int srcY, int remainingTurns) {
            super(EntityType.CANNONBALL, row, col);
            this.ownerEntityId = ownerEntityId;
            this.srcX = srcX;
            this.srcY = srcY;
            this.initialRemainingTurns = this.remainingTurns = remainingTurns;
        }

        public String toViewString() {
            return join(id, position.y, position.x, srcY, srcX, initialRemainingTurns, remainingTurns, ownerEntityId);
        }

        public String toPlayerString(int playerIdx) {
            return toPlayerString(ownerEntityId, remainingTurns, 0, 0);
        }
    }

    public static class RumBarrel extends Entity {
        private int health;

        public RumBarrel(int x, int y, int health) {
            super(EntityType.BARREL, x, y);
            this.health = health;
        }

        public String toViewString() {
            return join(id, position.y, position.x, health);
        }

        public String toPlayerString(int playerIdx) {
            return toPlayerString(health, 0, 0, 0);
        }
    }

    public static class Damage {
        private final Coord position;
        private final int health;
        private final boolean hit;

        public Damage(Coord position, int health, boolean hit) {
            this.position = position;
            this.health = health;
            this.hit = hit;
        }

        public String toViewString() {
            return join(position.y, position.x, health, (hit ? 1 : 0));
        }
    }

    public static enum Action {
        FASTER, SLOWER, PORT, STARBOARD, FIRE, MINE
    }

    public static class Ship extends Entity {
        int orientation;
        int speed;
        int health;
        int initialHealth;
        int owner;
        String message;
        Action action;
        int mineCooldown;
        int cannonCooldown;
        Coord target;
        public int newOrientation;
        public Coord newPosition;
        public Coord newBowCoordinate;
        public Coord newSternCoordinate;

        public Ship(int x, int y, int orientation, int owner) {
            super(EntityType.SHIP, x, y);
            this.orientation = orientation;
            this.speed = 0;
            this.health = INITIAL_SHIP_HEALTH;
            this.owner = owner;
        }

        public String toViewString() {
            return join(id, position.y, position.x, orientation, health, speed, (action != null ? action : "WAIT"), bow().y, bow().x, stern().y,
                    stern().x, " ;" + (message != null ? message : ""));
        }

        public String toPlayerString(int playerIdx) {
            return toPlayerString(orientation, speed, health, owner == playerIdx ? 1 : 0);
        }

        public void setMessage(String message) {
            if (message != null && message.length() > 50) {
                message = message.substring(0, 50) + "...";
            }
            this.message = message;
        }

        public void moveTo(int x, int y) {
            Coord currentPosition = this.position;
            Coord targetPosition = new Coord(x, y);

            if (currentPosition.equals(targetPosition)) {
                this.action = Action.SLOWER;
                return;
            }

            double targetAngle, angleStraight, anglePort, angleStarboard, centerAngle, anglePortCenter, angleStarboardCenter;

            switch (speed) {
            case 2:
                this.action = Action.SLOWER;
                break;
            case 1:
                // Suppose we've moved first
                currentPosition = currentPosition.neighbor(orientation);
                if (!currentPosition.isInsideMap()) {
                    this.action = Action.SLOWER;
                    break;
                }

                // Target reached at next turn
                if (currentPosition.equals(targetPosition)) {
                    this.action = null;
                    break;
                }

                // For each neighbor cell, find the closest to target
                targetAngle = currentPosition.angle(targetPosition);
                angleStraight = Math.min(Math.abs(orientation - targetAngle), 6 - Math.abs(orientation - targetAngle));
                anglePort = Math.min(Math.abs((orientation + 1) - targetAngle), Math.abs((orientation - 5) - targetAngle));
                angleStarboard = Math.min(Math.abs((orientation + 5) - targetAngle), Math.abs((orientation - 1) - targetAngle));

                centerAngle = currentPosition.angle(new Coord(MAP_WIDTH / 2, MAP_HEIGHT / 2));
                anglePortCenter = Math.min(Math.abs((orientation + 1) - centerAngle), Math.abs((orientation - 5) - centerAngle));
                angleStarboardCenter = Math.min(Math.abs((orientation + 5) - centerAngle), Math.abs((orientation - 1) - centerAngle));

                // Next to target with bad angle, slow down then rotate (avoid to turn around the target!)
                if (currentPosition.distanceTo(targetPosition) == 1 && angleStraight > 1.5) {
                    this.action = Action.SLOWER;
                    break;
                }

                Integer distanceMin = null;

                // Test forward
                Coord nextPosition = currentPosition.neighbor(orientation);
                if (nextPosition.isInsideMap()) {
                    distanceMin = nextPosition.distanceTo(targetPosition);
                    this.action = null;
                }

                // Test port
                nextPosition = currentPosition.neighbor((orientation + 1) % 6);
                if (nextPosition.isInsideMap()) {
                    int distance = nextPosition.distanceTo(targetPosition);
                    if (distanceMin == null || distance < distanceMin || distance == distanceMin && anglePort < angleStraight - 0.5) {
                        distanceMin = distance;
                        this.action = Action.PORT;
                    }
                }

                // Test starboard
                nextPosition = currentPosition.neighbor((orientation + 5) % 6);
                if (nextPosition.isInsideMap()) {
                    int distance = nextPosition.distanceTo(targetPosition);
                    if (distanceMin == null || distance < distanceMin
                            || (distance == distanceMin && angleStarboard < anglePort - 0.5 && this.action == Action.PORT)
                            || (distance == distanceMin && angleStarboard < angleStraight - 0.5 && this.action == null)
                            || (distance == distanceMin && this.action == Action.PORT && angleStarboard == anglePort
                                    && angleStarboardCenter < anglePortCenter)
                            || (distance == distanceMin && this.action == Action.PORT && angleStarboard == anglePort
                                    && angleStarboardCenter == anglePortCenter && (orientation == 1 || orientation == 4))) {
                        distanceMin = distance;
                        this.action = Action.STARBOARD;
                    }
                }
                break;
            case 0:
                // Rotate ship towards target
                targetAngle = currentPosition.angle(targetPosition);
                angleStraight = Math.min(Math.abs(orientation - targetAngle), 6 - Math.abs(orientation - targetAngle));
                anglePort = Math.min(Math.abs((orientation + 1) - targetAngle), Math.abs((orientation - 5) - targetAngle));
                angleStarboard = Math.min(Math.abs((orientation + 5) - targetAngle), Math.abs((orientation - 1) - targetAngle));

                centerAngle = currentPosition.angle(new Coord(MAP_WIDTH / 2, MAP_HEIGHT / 2));
                anglePortCenter = Math.min(Math.abs((orientation + 1) - centerAngle), Math.abs((orientation - 5) - centerAngle));
                angleStarboardCenter = Math.min(Math.abs((orientation + 5) - centerAngle), Math.abs((orientation - 1) - centerAngle));

                Coord forwardPosition = currentPosition.neighbor(orientation);

                this.action = null;

                if (anglePort <= angleStarboard) {
                    this.action = Action.PORT;
                }

                if (angleStarboard < anglePort || angleStarboard == anglePort && angleStarboardCenter < anglePortCenter
                        || angleStarboard == anglePort && angleStarboardCenter == anglePortCenter && (orientation == 1 || orientation == 4)) {
                    this.action = Action.STARBOARD;
                }

                if (forwardPosition.isInsideMap() && angleStraight <= anglePort && angleStraight <= angleStarboard) {
                    this.action = Action.FASTER;
                }
                break;
            }

        }

        public void faster() {
            this.action = Action.FASTER;
        }

        public void slower() {
            this.action = Action.SLOWER;
        }

        public void port() {
            this.action = Action.PORT;
        }

        public void starboard() {
            this.action = Action.STARBOARD;
        }

        public void placeMine() {
            if (MINES_ENABLED) {
                this.action = Action.MINE;
            }
        }

        public Coord stern() {
            return position.neighbor((orientation + 3) % 6);
        }

        public Coord bow() {
            return position.neighbor(orientation);
        }

        public Coord newStern() {
            return position.neighbor((newOrientation + 3) % 6);
        }

        public Coord newBow() {
            return position.neighbor(newOrientation);
        }

        public boolean at(Coord coord) {
            Coord stern = stern();
            Coord bow = bow();
            return stern != null && stern.equals(coord) || bow != null && bow.equals(coord) || position.equals(coord);
        }

        public boolean newBowIntersect(Ship other) {
            return newBowCoordinate != null && (newBowCoordinate.equals(other.newBowCoordinate) || newBowCoordinate.equals(other.newPosition)
                    || newBowCoordinate.equals(other.newSternCoordinate));
        }

        public boolean newBowIntersect(List<Ship> ships) {
            for (Ship other : ships) {
                if (this != other && newBowIntersect(other)) {
                    return true;
                }
            }
            return false;
        }

        public boolean newPositionsIntersect(Ship other) {
            boolean sternCollision = newSternCoordinate != null && (newSternCoordinate.equals(other.newBowCoordinate)
                    || newSternCoordinate.equals(other.newPosition) || newSternCoordinate.equals(other.newSternCoordinate));
            boolean centerCollision = newPosition != null && (newPosition.equals(other.newBowCoordinate) || newPosition.equals(other.newPosition)
                    || newPosition.equals(other.newSternCoordinate));
            return newBowIntersect(other) || sternCollision || centerCollision;
        }

        public boolean newPositionsIntersect(List<Ship> ships) {
            for (Ship other : ships) {
                if (this != other && newPositionsIntersect(other)) {
                    return true;
                }
            }
            return false;
        }

        public void damage(int health) {
            this.health -= health;
            if (this.health <= 0) {
                this.health = 0;
            }
        }

        public void heal(int health) {
            this.health += health;
            if (this.health > MAX_SHIP_HEALTH) {
                this.health = MAX_SHIP_HEALTH;
            }
        }

        public void fire(int x, int y) {
            if (CANNONS_ENABLED) {
                Coord target = new Coord(x, y);
                this.target = target;
                this.action = Action.FIRE;
            }
        }
    }

    private static class Player {
        private int id;
        private List<Ship> ships;
        private List<Ship> shipsAlive;

        public Player(int id) {
            this.id = id;
            this.ships = new ArrayList<>();
            this.shipsAlive = new ArrayList<>();
        }

        public void setDead() {
            for (Ship ship : ships) {
                ship.health = 0;
            }
        }

        public int getScore() {
            int score = 0;
            for (Ship ship : ships) {
                score += ship.health;
            }
            return score;
        }

        public List<String> toViewString() {
            List<String> data = new ArrayList<>();

            data.add(String.valueOf(this.id));
            for (Ship ship : ships) {
                data.add(ship.toViewString());
            }

            return data;
        }
    }

    private long seed;
    private List<Cannonball> cannonballs;
    private List<Mine> mines;
    private List<RumBarrel> barrels;
    private List<Player> players;
    private List<Ship> ships;
    private List<Damage> damage;
    private List<Coord> cannonBallExplosions;
    private int shipsPerPlayer;
    private int mineCount;
    private int barrelCount;
    private Random random;

    public Referee(InputStream is, PrintStream out, PrintStream err) throws IOException {
        super(is, out, err);
    }

    public static void main(String... args) throws IOException {
        new Referee(System.in, System.out, System.err);
    }

    @Override
    protected void initReferee(int playerCount, Properties prop) throws InvalidFormatException {
        seed = parseProperty(prop, "seed", new Random(System.currentTimeMillis()).nextLong());

        random = new Random(this.seed);

        shipsPerPlayer = clamp((int) parseProperty(prop, "shipsPerPlayer", random.nextInt(1 + MAX_SHIPS - MIN_SHIPS) + MIN_SHIPS), MIN_SHIPS,
                MAX_SHIPS);

        if (MAX_MINES > MIN_MINES) {
            mineCount = clamp((int) parseProperty(prop, "mineCount", random.nextInt(MAX_MINES - MIN_MINES) + MIN_MINES), MIN_MINES, MAX_MINES);
        } else {
            mineCount = MIN_MINES;
        }

        barrelCount = clamp((int) parseProperty(prop, "barrelCount", random.nextInt(MAX_RUM_BARRELS - MIN_RUM_BARRELS) + MIN_RUM_BARRELS),
                MIN_RUM_BARRELS, MAX_RUM_BARRELS);

        cannonballs = new ArrayList<>();
        cannonBallExplosions = new ArrayList<>();
        damage = new ArrayList<>();

        // Generate Players
        this.players = new ArrayList<Player>(playerCount);
        for (int i = 0; i < playerCount; i++) {
            this.players.add(new Player(i));
        }
        // Generate Ships
        for (int j = 0; j < shipsPerPlayer; j++) {
            int xMin = 1 + j * MAP_WIDTH / shipsPerPlayer;
            int xMax = (j + 1) * MAP_WIDTH / shipsPerPlayer - 2;

            int y = 1 + random.nextInt(MAP_HEIGHT / 2 - 2);
            int x = xMin + random.nextInt(1 + xMax - xMin);
            int orientation = random.nextInt(6);

            Ship ship0 = new Ship(x, y, orientation, 0);
            Ship ship1 = new Ship(x, MAP_HEIGHT - 1 - y, (6 - orientation) % 6, 1);

            this.players.get(0).ships.add(ship0);
            this.players.get(1).ships.add(ship1);
            this.players.get(0).shipsAlive.add(ship0);
            this.players.get(1).shipsAlive.add(ship1);
        }

        this.ships = players.stream().map(p -> p.ships).flatMap(List::stream).collect(Collectors.toList());

        // Generate mines
        mines = new ArrayList<>();
        while (mines.size() < mineCount) {
            int x = 1 + random.nextInt(MAP_WIDTH - 2);
            int y = 1 + random.nextInt(MAP_HEIGHT / 2);

            Mine m = new Mine(x, y);

            boolean cellIsFreeOfMines = mines.stream().noneMatch(mine -> mine.position.equals(m.position));
            boolean cellIsFreeOfShips = ships.stream().noneMatch(ship -> ship.at(m.position));

            if (cellIsFreeOfShips && cellIsFreeOfMines) {
                if (y != MAP_HEIGHT - 1 - y) {
                    mines.add(new Mine(x, MAP_HEIGHT - 1 - y));
                }
                mines.add(m);
            }
        }
        mineCount = mines.size();

        // Generate supplies
        barrels = new ArrayList<>();
        while (barrels.size() < barrelCount) {
            int x = 1 + random.nextInt(MAP_WIDTH - 2);
            int y = 1 + random.nextInt(MAP_HEIGHT / 2);
            int h = MIN_RUM_BARREL_VALUE + random.nextInt(1 + MAX_RUM_BARREL_VALUE - MIN_RUM_BARREL_VALUE);

            RumBarrel m = new RumBarrel(x, y, h);

            boolean cellIsFreeOfBarrels = barrels.stream().noneMatch(barrel -> barrel.position.equals(m.position));
            boolean cellIsFreeOfMines = mines.stream().noneMatch(mine -> mine.position.equals(m.position));
            boolean cellIsFreeOfShips = ships.stream().noneMatch(ship -> ship.at(m.position));

            if (cellIsFreeOfShips && cellIsFreeOfMines && cellIsFreeOfBarrels) {
                if (y != MAP_HEIGHT - 1 - y) {
                    barrels.add(new RumBarrel(x, MAP_HEIGHT - 1 - y, h));
                }
                barrels.add(m);
            }
        }
        barrelCount = barrels.size();

    }

    @Override
    protected Properties getConfiguration() {
        Properties prop = new Properties();
        prop.setProperty("seed", String.valueOf(seed));
        prop.setProperty("shipsPerPlayer", String.valueOf(shipsPerPlayer));
        prop.setProperty("barrelCount", String.valueOf(barrelCount));
        prop.setProperty("mineCount", String.valueOf(mineCount));
        return prop;
    }

    @Override
    protected void prepare(int round) {
        for (Player player : players) {
            for (Ship ship : player.ships) {
                ship.action = null;
                ship.message = null;
            }
        }
        cannonBallExplosions.clear();
        damage.clear();
    }

    @Override
    protected int getExpectedOutputLineCountForPlayer(int playerIdx) {
        return this.players.get(playerIdx).shipsAlive.size();
    }

    @Override
    protected void handlePlayerOutput(int frame, int round, int playerIdx, String[] outputs)
            throws WinException, LostException, InvalidInputException {
        Player player = this.players.get(playerIdx);

        try {
            int i = 0;
            for (String line : outputs) {
                Matcher matchWait = PLAYER_INPUT_WAIT_PATTERN.matcher(line);
                Matcher matchMove = PLAYER_INPUT_MOVE_PATTERN.matcher(line);
                Matcher matchFaster = PLAYER_INPUT_FASTER_PATTERN.matcher(line);
                Matcher matchSlower = PLAYER_INPUT_SLOWER_PATTERN.matcher(line);
                Matcher matchPort = PLAYER_INPUT_PORT_PATTERN.matcher(line);
                Matcher matchStarboard = PLAYER_INPUT_STARBOARD_PATTERN.matcher(line);
                Matcher matchFire = PLAYER_INPUT_FIRE_PATTERN.matcher(line);
                Matcher matchMine = PLAYER_INPUT_MINE_PATTERN.matcher(line);
                Ship ship = player.shipsAlive.get(i++);

                if (matchMove.matches()) {
                    int x = Integer.parseInt(matchMove.group("x"));
                    int y = Integer.parseInt(matchMove.group("y"));
                    ship.setMessage(matchMove.group("message"));
                    ship.moveTo(x, y);
                } else if (matchFaster.matches()) {
                    ship.setMessage(matchFaster.group("message"));
                    ship.faster();
                } else if (matchSlower.matches()) {
                    ship.setMessage(matchSlower.group("message"));
                    ship.slower();
                } else if (matchPort.matches()) {
                    ship.setMessage(matchPort.group("message"));
                    ship.port();
                } else if (matchStarboard.matches()) {
                    ship.setMessage(matchStarboard.group("message"));
                    ship.starboard();
                } else if (matchWait.matches()) {
                    ship.setMessage(matchWait.group("message"));
                } else if (matchMine.matches()) {
                    ship.setMessage(matchMine.group("message"));
                    ship.placeMine();
                } else if (matchFire.matches()) {
                    int x = Integer.parseInt(matchFire.group("x"));
                    int y = Integer.parseInt(matchFire.group("y"));
                    ship.setMessage(matchFire.group("message"));
                    ship.fire(x, y);
                } else {
                    throw new InvalidInputException("A valid action", line);
                }
            }
        } catch (InvalidInputException e) {
            player.setDead();
            throw e;
        }
    }

    private void decrementRum() {
        for (Ship ship : ships) {
            ship.damage(1);
        }
    }

    private void updateInitialRum() {
        for (Ship ship : ships) {
            ship.initialHealth = ship.health;
        }
    }

    private void moveCannonballs() {
        for (Iterator<Cannonball> it = cannonballs.iterator(); it.hasNext();) {
            Cannonball ball = it.next();
            if (ball.remainingTurns == 0) {
                it.remove();
                continue;
            } else if (ball.remainingTurns > 0) {
                ball.remainingTurns--;
            }

            if (ball.remainingTurns == 0) {
                cannonBallExplosions.add(ball.position);
            }
        }
    }

    private void applyActions() {
        for (Player player : players) {
            for (Ship ship : player.shipsAlive) {
                if (ship.mineCooldown > 0) {
                    ship.mineCooldown--;
                }
                if (ship.cannonCooldown > 0) {
                    ship.cannonCooldown--;
                }

                ship.newOrientation = ship.orientation;

                if (ship.action != null) {
                    switch (ship.action) {
                    case FASTER:
                        if (ship.speed < MAX_SHIP_SPEED) {
                            ship.speed++;
                        }
                        break;
                    case SLOWER:
                        if (ship.speed > 0) {
                            ship.speed--;
                        }
                        break;
                    case PORT:
                        ship.newOrientation = (ship.orientation + 1) % 6;
                        break;
                    case STARBOARD:
                        ship.newOrientation = (ship.orientation + 5) % 6;
                        break;
                    case MINE:
                        if (ship.mineCooldown == 0) {
                            Coord target = ship.stern().neighbor((ship.orientation + 3) % 6);

                            if (target.isInsideMap()) {
                                boolean cellIsFreeOfBarrels = barrels.stream().noneMatch(barrel -> barrel.position.equals(target));
                                boolean cellIsFreeOfMines = mines.stream().noneMatch(mine -> mine.position.equals(target));
                                boolean cellIsFreeOfShips = ships.stream().filter(b -> b != ship).noneMatch(b -> b.at(target));

                                if (cellIsFreeOfBarrels && cellIsFreeOfShips && cellIsFreeOfMines) {
                                    ship.mineCooldown = COOLDOWN_MINE;
                                    Mine mine = new Mine(target.x, target.y);
                                    mines.add(mine);
                                }
                            }

                        }
                        break;
                    case FIRE:
                        int distance = ship.bow().distanceTo(ship.target);
                        if (ship.target.isInsideMap() && distance <= FIRE_DISTANCE_MAX && ship.cannonCooldown == 0) {
                            int travelTime = (int) (1 + Math.round(ship.bow().distanceTo(ship.target) / 3.0));
                            cannonballs.add(new Cannonball(ship.target.x, ship.target.y, ship.id, ship.bow().x, ship.bow().y, travelTime));
                            ship.cannonCooldown = COOLDOWN_CANNON;
                        }
                        break;
                    default:
                        break;
                    }
                }
            }
        }
    }

    private void checkBarrelCollisions(Ship ship) {
        Coord bow = ship.bow();
        Coord stern = ship.stern();
        Coord center = ship.position;

        for (Iterator<RumBarrel> it = barrels.iterator(); it.hasNext();) {
            RumBarrel barrel = it.next();
            if (barrel.position.equals(bow) || barrel.position.equals(stern) || barrel.position.equals(center)) {
                ship.heal(barrel.health);
                it.remove();
            }
        }
    }

    private void checkMineCollisions() {
        for (Iterator<Mine> it = mines.iterator(); it.hasNext();) {
            Mine mine = it.next();
            List<Damage> mineDamage = mine.explode(ships, false);

            if (!mineDamage.isEmpty()) {
                damage.addAll(mineDamage);
                it.remove();
            }
        }
    }

    private void checkCollisions() {
        // Check collisions with Barrels
        for (Ship ship : this.ships) {
            checkBarrelCollisions(ship);
        }

        // Check collisions with Mines
        checkMineCollisions();
    }

    private void moveShips() {
        // ---
        // Go forward
        // ---
        for (int i = 1; i <= MAX_SHIP_SPEED; i++) {
            for (Player player : players) {
                for (Ship ship : player.shipsAlive) {
                    ship.newPosition = ship.position;
                    ship.newBowCoordinate = ship.bow();
                    ship.newSternCoordinate = ship.stern();

                    if (i > ship.speed) {
                        continue;
                    }

                    Coord newCoordinate = ship.position.neighbor(ship.orientation);

                    if (newCoordinate.isInsideMap()) {
                        // Set new coordinate.
                        ship.newPosition = newCoordinate;
                        ship.newBowCoordinate = newCoordinate.neighbor(ship.orientation);
                        ship.newSternCoordinate = newCoordinate.neighbor((ship.orientation + 3) % 6);
                    } else {
                        // Stop ship!
                        ship.speed = 0;
                    }
                }
            }

            // Check ship and obstacles collisions
            List<Ship> collisions = new ArrayList<>();
            boolean collisionDetected = true;
            while (collisionDetected) {
                collisionDetected = false;

                for (Ship ship : this.ships) {
                    if (ship.newBowIntersect(ships)) {
                        collisions.add(ship);
                    }
                }

                for (Ship ship : collisions) {
                    // Revert last move
                    ship.newPosition = ship.position;
                    ship.newBowCoordinate = ship.bow();
                    ship.newSternCoordinate = ship.stern();

                    // Stop ships
                    ship.speed = 0;

                    collisionDetected = true;
                }
                collisions.clear();
            }

            // Move ships to their new location
            for (Ship ship : this.ships) {
                ship.position = ship.newPosition;
            }

            checkCollisions();
        }
    }

    private void rotateShips() {
        // Rotate
        for (Player player : players) {
            for (Ship ship : player.shipsAlive) {
                ship.newPosition = ship.position;
                ship.newBowCoordinate = ship.newBow();
                ship.newSternCoordinate = ship.newStern();
            }
        }

        // Check collisions
        boolean collisionDetected = true;
        List<Ship> collisions = new ArrayList<>();
        while (collisionDetected) {
            collisionDetected = false;

            for (Ship ship : this.ships) {
                if (ship.newPositionsIntersect(ships)) {
                    collisions.add(ship);
                }
            }

            for (Ship ship : collisions) {
                ship.newOrientation = ship.orientation;
                ship.newBowCoordinate = ship.newBow();
                ship.newSternCoordinate = ship.newStern();
                ship.speed = 0;
                collisionDetected = true;
            }

            collisions.clear();
        }

        // Apply rotation
        for (Ship ship : this.ships) {
            ship.orientation = ship.newOrientation;
        }

        checkCollisions();
    }

    private boolean gameIsOver() {
        for (Player player : players) {
            if (player.shipsAlive.isEmpty()) {
                return true;
            }
        }
        return barrels.size() == 0 && LEAGUE_LEVEL == 0;
    }

    void explodeShips() {
        for (Iterator<Coord> it = cannonBallExplosions.iterator(); it.hasNext();) {
            Coord position = it.next();
            for (Ship ship : ships) {
                if (position.equals(ship.bow()) || position.equals(ship.stern())) {
                    damage.add(new Damage(position, LOW_DAMAGE, true));
                    ship.damage(LOW_DAMAGE);
                    it.remove();
                    break;
                } else if (position.equals(ship.position)) {
                    damage.add(new Damage(position, HIGH_DAMAGE, true));
                    ship.damage(HIGH_DAMAGE);
                    it.remove();
                    break;
                }
            }
        }
    }

    void explodeMines() {
        for (Iterator<Coord> itBall = cannonBallExplosions.iterator(); itBall.hasNext();) {
            Coord position = itBall.next();
            for (Iterator<Mine> it = mines.iterator(); it.hasNext();) {
                Mine mine = it.next();
                if (mine.position.equals(position)) {
                    damage.addAll(mine.explode(ships, true));
                    it.remove();
                    itBall.remove();
                    break;
                }
            }
        }
    }

    void explodeBarrels() {
        for (Iterator<Coord> itBall = cannonBallExplosions.iterator(); itBall.hasNext();) {
            Coord position = itBall.next();
            for (Iterator<RumBarrel> it = barrels.iterator(); it.hasNext();) {
                RumBarrel barrel = it.next();
                if (barrel.position.equals(position)) {
                    damage.add(new Damage(position, 0, true));
                    it.remove();
                    itBall.remove();
                    break;
                }
            }
        }
    }

    @Override
    protected void updateGame(int round) throws GameOverException {
        moveCannonballs();
        decrementRum();
        updateInitialRum();

        applyActions();
        moveShips();
        rotateShips();

        explodeShips();
        explodeMines();
        explodeBarrels();

        // For each sunk ship, create a new rum barrel with the amount of rum the ship had at the begin of the turn (up to 30).
        for (Ship ship : ships) {
            if (ship.health <= 0) {
                int reward = Math.min(REWARD_RUM_BARREL_VALUE, ship.initialHealth);
                if (reward > 0) {
                    barrels.add(new RumBarrel(ship.position.x, ship.position.y, reward));
                }
            }
        }

        for (Coord position : cannonBallExplosions) {
            damage.add(new Damage(position, 0, false));
        }

        for (Iterator<Ship> it = ships.iterator(); it.hasNext();) {
            Ship ship = it.next();
            if (ship.health <= 0) {
                players.get(ship.owner).shipsAlive.remove(ship);
                it.remove();
            }
        }

        if (gameIsOver()) {
            throw new GameOverException("endReached");
        }
    }

    @Override
    protected void populateMessages(Properties p) {
        p.put("endReached", "End reached");
    }

    @Override
    protected String[] getInitInputForPlayer(int playerIdx) {
        return new String[0];
    }

    @Override
    protected String[] getInputForPlayer(int round, int playerIdx) {
        List<String> data = new ArrayList<>();

        // Player's ships first
        for (Ship ship : players.get(playerIdx).shipsAlive) {
            data.add(ship.toPlayerString(playerIdx));
        }

        // Number of ships
        data.add(0, String.valueOf(data.size()));

        // Opponent's ships
        for (Ship ship : players.get((playerIdx + 1) % 2).shipsAlive) {
            data.add(ship.toPlayerString(playerIdx));
        }

        // Visible mines
        for (Mine mine : mines) {
            boolean visible = false;
            for (Ship ship : players.get(playerIdx).shipsAlive) {
                if (ship.position.distanceTo(mine.position) <= MINE_VISIBILITY_RANGE) {
                    visible = true;
                    break;
                }
            }
            if (visible) {
                data.add(mine.toPlayerString(playerIdx));
            }
        }

        for (Cannonball ball : cannonballs) {
            data.add(ball.toPlayerString(playerIdx));
        }

        for (RumBarrel barrel : barrels) {
            data.add(barrel.toPlayerString(playerIdx));
        }

        data.add(1, String.valueOf(data.size() - 1));

        return data.toArray(new String[data.size()]);
    }

    @Override
    protected String[] getInitDataForView() {
        List<String> data = new ArrayList<>();

        data.add(join(MAP_WIDTH, MAP_HEIGHT, players.get(0).ships.size(), MINE_VISIBILITY_RANGE));

        data.add(0, String.valueOf(data.size() + 1));

        return data.toArray(new String[data.size()]);
    }

    @Override
    protected String[] getFrameDataForView(int round, int frame, boolean keyFrame) {
        List<String> data = new ArrayList<>();

        for (Player player : players) {
            data.addAll(player.toViewString());
        }
        data.add(String.valueOf(cannonballs.size()));
        for (Cannonball ball : cannonballs) {
            data.add(ball.toViewString());
        }
        data.add(String.valueOf(mines.size()));
        for (Mine mine : mines) {
            data.add(mine.toViewString());
        }
        data.add(String.valueOf(barrels.size()));
        for (RumBarrel barrel : barrels) {
            data.add(barrel.toViewString());
        }
        data.add(String.valueOf(damage.size()));
        for (Damage d : damage) {
            data.add(d.toViewString());
        }

        return data.toArray(new String[data.size()]);
    }

    @Override
    protected String getGameName() {
        return "CodersOfTheCaribbean";
    }

    @Override
    protected String getHeadlineAtGameStartForConsole() {
        return null;
    }

    @Override
    protected int getMinimumPlayerCount() {
        return 2;
    }

    @Override
    protected boolean showTooltips() {
        return true;
    }

    @Override
    protected String[] getPlayerActions(int playerIdx, int round) {
        return new String[0];
    }

    @Override
    protected boolean isPlayerDead(int playerIdx) {
        return false;
    }

    @Override
    protected String getDeathReason(int playerIdx) {
        return "$" + playerIdx + ": Eliminated!";
    }

    @Override
    protected int getScore(int playerIdx) {
        return players.get(playerIdx).getScore();
    }

    @Override
    protected String[] getGameSummary(int round) {
        return new String[0];
    }

    @Override
    protected void setPlayerTimeout(int frame, int round, int playerIdx) {
        players.get(playerIdx).setDead();
    }

    @Override
    protected int getMaxRoundCount(int playerCount) {
        return 200;
    }

    @Override
    protected int getMillisTimeForRound() {
        return 50;
    }
}
