#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
#define pu push
#define pb push_back
#define mp make_pair
#define eps 1e-10
#define Vector Point
#define Points vector<Point>
#define INF 2000000000
#define DOUBLE_INF 1e50
#define sq(x) ((x)*(x))
#define fi first
#define sec second
#define all(x) (x).begin(),(x).end()
#define EQ(a,b) (abs((a)-(b))<eps)

// Geometry Library
// written by okuraofvegetable

inline double add(double a,double b){
	if(abs(a+b)<eps*(abs(a)+abs(b)))return 0;
	return a+b;
}

struct Point{
	double x,y;
	Point() {}
	Point(double x,double y) : x(x),y(y){}
	Point operator + (Point p){return Point(add(x,p.x),add(y,p.y));}
	Point operator - (Point p){return Point(add(x,-p.x),add(y,-p.y));}
	Point operator * (double d){return Point(x*d,y*d);}
	Point operator / (double d){return Point(x/d,y/d);}
	double dot(Point p){return add(x*p.x,y*p.y);}
	double det(Point p){return add(x*p.y,-y*p.x);}
	double norm(){return sqrt(x*x+y*y);}
	double norm2(){return x*x+y*y;}
	double dist(Point p){return ((*this)-p).norm();}
	double dist2(Point p){return sq(x-p.x)+sq(y-p.y);}
	double arg(){return atan2(y,x);}                        // [-PI,PI]
	double arg(Vector v){return v.arg()-arg();}             // henkaku
	double angle(Vector v){                                 // [0,PI]
		return acos(cos(arg(v)));
	}
	Vector normalize(){return (*this)*(1.0/norm());}
	Point vert(){return Point(y,-x);}
	void dump(const char* msg=""){printf("%s%.12f %.12f\n",msg,x,y);return;}

	// signed area of triange (0,0) (x,y) (p.x,p.y)
	double area(Point p){
		return (x*p.y-p.x*y)/2.0;
	}
};
// direction a -> b -> c
// verified AOJ CGL_1_C
enum {
	COUNTER_CLOCKWISE,
	CLOCKWISE,
	ONLINE_BACK,
	ONLINE_FRONT,
	ON_SEGMENT
};
Point divide_rate(Point a,Point b,double A,double B){
	assert(!EQ(A+B,0.0));
	return (a*B+b*A)*(1.0/(A+B));
}
Vector polar(double len,double arg){
	return Vector(cos(arg)*len,sin(arg)*len);
}
int ccw(Point a,Point b,Point c){
	Vector p = b-a;
	Vector q = c-a;
	if(p.det(q)>0.0)return COUNTER_CLOCKWISE; // counter clockwise
	if(p.det(q)<0.0)return CLOCKWISE; // clockwise
	if(p.dot(q)<0.0)return ONLINE_BACK; // c--a--b online_back
	if(p.norm()<q.norm())return ONLINE_FRONT; // a--b--c online_front 
	return ON_SEGMENT;// a--c--b on_segment
}
struct Line{
	Point a,b;
	Line(){}
	Line(Point a,Point b):a(a),b(b){}
	bool on(Point q){
		return (a-q).det(b-q)==0; 
	}
	// folloing 2 functions verified AOJ CGL_2_A
	bool is_parallel(Line l){return (a-b).det(l.a-l.b)==0;}
	bool is_orthogonal(Line l){return (a-b).dot(l.a-l.b)==0;}
	Point intersection(Line l){
		assert(!is_parallel(l));
		return a+(b-a)*((l.b-l.a).det(l.a-a)/(l.b-l.a).det(b-a));
	}
	// projection of p to this line
	// verified AOJ CGL_1_A
	Point projection(Point p){
		return (b-a)*((b-a).dot(p-a)/(b-a).norm2())+a;
	}
	double distance(Point p){
		Point q = projection(p);
		return p.dist(q);
	}
	// reflection point of p onto this line
	// verified AOJ CGL_1_B
	Point refl(Point p){
		Point proj = projection(p);
		return p+((proj-p)*2.0);
	}
	bool left(Point p){
		if((p-a).det(b-a)>0.0)return true;
		else return false;
	}
};
struct Segment{
	Point a,b;
	Segment(){}
	Segment(Point a,Point b):a(a),b(b){}
	Line line(){
		return Line(a,b);
	}
	bool on(Point q){
		return ((a-q).det(b-q)==0&&(a-q).dot(b-q)<=0); 
	}
	// verified AOJ CGL_2_B
	bool is_intersect(Segment s){
		if(line().is_parallel(s.line())){
			if(on(s.a)||on(s.b))return true;
			if(s.on(a)||s.on(b))return true;
			return false;
		}
		Point p = line().intersection(s.line());
		if(on(p)&&s.on(p))return true;
		else return false;
	}
	bool is_intersect(Line l){
		if(line().is_parallel(l)){
			if(l.on(a)||l.on(b))return true;
			else return false;
		}
		Point p = line().intersection(l);
		if(on(p))return true;
		else return false;
	}
	// following 2 distance functions verified AOJ CGL_2_D
	double distance(Point p){
		double res = DOUBLE_INF;
		Point q = line().projection(p);
		if(on(q))res = min(res,p.dist(q));
		res = min(res,min(p.dist(a),p.dist(b)));
		return res;
	}
	double distance(Segment s){
		if(is_intersect(s))return 0.0;
		double res = DOUBLE_INF;
		res = min(res,s.distance(a));
		res = min(res,s.distance(b));
		res = min(res,this->distance(s.a));
		res = min(res,this->distance(s.b));
		return res;
	}
};

// Polygon 

typedef vector<Point> Polygon;
// verified AOJ CGL_3_A
// Polygon don't need to be convex
double area(Polygon& pol){
	Points vec;
	double res = 0.0;
	int M = pol.size();
	for(int i=0;i<M;i++){
		res += (pol[i]-pol[0]).area(pol[(i+1)%M]-pol[0]);	
	}
	return res;
}
bool is_convex(Polygon& pol){
	int n = pol.size();
	for(int i=0;i<n-1;i++){
		if(ccw(pol[i],pol[i+1],pol[(i+2)%n])==CLOCKWISE){
			return false;
		}
	}
	return true;
}
// vecrified AOJ CGL_3_C
enum {OUT,ON,IN};
int contained(Polygon& pol,Point p){
	int n = pol.size();
	Point outer(1e9,p.y);
	Segment s = Segment(outer,p);
	int cnt = 0;
	for(int i=0;i<n;i++){
		Segment e = Segment(pol[i],pol[(i+1)%n]);
		if(e.on(p))return ON;
		Vector a = pol[i]-p;
		Vector b = pol[(i+1)%n]-p;
		if(a.y>b.y)swap(a,b);
		if(a.y<=0.0&&b.y>0.0){
			if(a.det(b)<0.0)cnt++;
		}
	}
	if((cnt&1)==1)return IN;
	else return OUT;
}
// compare function for convex_hull
// sort points by (x-y) lexicographical order.
// you can change (y-x) order with no change in convex_hull
bool comp(const Point& p,const Point& q){
	if(p.x!=q.x)return p.x<q.x;
	else return p.y<q.y;
}
// Convex hull
// if you want not to contain points on boundary,
// change while(....<=0.0)
// verified AOJ CGL_4_A
Polygon convex_hull(vector<Point> ps){
	sort(all(ps),comp);
	int k = 0;
	int n = ps.size();
	Polygon qs(2*n);
	for(int i=0;i<n;i++){
		while(k>1&&(qs[k-1]-qs[k-2]).det(ps[i]-qs[k-1])<0.0)k--;
		qs[k++]=ps[i];
	}
	for(int i=n-2,t=k;i>=0;i--){
		while(k>t&&(qs[k-1]-qs[k-2]).det(ps[i]-qs[k-1])<0.0)k--;
		qs[k++]=ps[i];
	}
	qs.resize(k-1);
	return qs;
}
// Caliper method
// verified AOJ CGL_4_B
double convex_diameter(Polygon& cv){
	int i=0,j=0;
	int n = cv.size();
	for(int k=0;k<n;k++){
		if(!comp(cv[i],cv[k]))i=k;
		if(comp(cv[j],cv[k]))j=k;
	}
	int si=i,sj=j;
	double res = 0.0;
	while(i!=sj||j!=si){
		res = max(res,cv[i].dist(cv[j]));
		if((cv[(i+1)%n]-cv[i]).det(cv[(j+1)%n]-cv[j])<0.0)i=(i+1)%n;
		else j=(j+1)%n;
	}
	return res;
}
// Cut conovex polygon by a line and return left polygon
// verified AOJ CGL_4_C
Polygon convex_cut(Polygon& cv,Line l){
	int n = cv.size();
	Polygon left; 
	for(int i=0;i<n;i++){
		Segment e = Segment(cv[i],cv[(i+1)%n]);
		if(ccw(l.a,l.b,cv[i])!=CLOCKWISE)left.pb(cv[i]);
		if(e.is_intersect(l)){
			if(!e.line().is_parallel(l)){
				left.pb(e.line().intersection(l));
			}
		}
	}
	return left;
}
// distance between closest pair
// verified CGL_5_A
bool comp_y(const Point& p,const Point& q){
	return p.y<q.y;
}
double closest_pair(vector<Point>::iterator a,int n){
	if(n<=1)return DOUBLE_INF;
	int m = n/2;
	double x = (a+m)->x;
	double d = min(closest_pair(a,m),closest_pair(a+m,n-m));
	inplace_merge(a,a+m,a+n,comp_y);
	vector<Point> b;
	for(int i=0;i<n;i++){
		double ax = (a+i)->x;
		double ay = (a+i)->y;
		if(abs(ax-x)>=d)continue;
		for(int j=0;j<b.size();j++){
			double dx = ax-b[b.size()-1-j].x;
			double dy = ay-b[b.size()-1-j].y;
			if(dy>=d)break;
			d = min(d,sqrt(dx*dx+dy*dy));
		}
		b.pb(*(a+i));
	}
	return d;
}
double closest_pair(vector<Point> a){
	sort(all(a),comp);
	return closest_pair(a.begin(),(int)a.size());
}

// Circle

// relation between two circles
// each value as integer corresponds to
// the number of common tangent lines
enum {
	INCLUDE,
	INSCRIBED,         // in japanese "naisetsu"
	INTERSECT,
	CIRCUMSCRIBED,     // in japanese "gaisetsu"
	NOT_CROSS,
};

struct Circle{
	Point center;
	double r;
	Circle(){}
	Circle(Point c,double r):center(c),r(r){}
	bool in(Point p){
		return p.dist(center)<r;
	}
	// verified AOJ CGL_7_A
	int is_intersect(Circle c){
		double cd = center.dist(c.center);
		if(EQ(cd,r+c.r))return CIRCUMSCRIBED;
		if(EQ(cd,abs(r-c.r)))return INSCRIBED;
		if(cd>r+c.r)return NOT_CROSS;
		else if(cd>abs(r-c.r))return INTERSECT;
		else return INCLUDE;
	}
	// verified AOJ CGL_7_D
	Points intersection(Line l){
		Points res;
		double d = l.distance(center);
		if(EQ(d,r)){
			res.pb(l.projection(center));
		}else if(d<r){
			double k = sqrt(r*r-d*d);
			Vector v = (l.a-l.b).normalize()*k;
			res.pb(l.projection(center)+v);
			res.pb(l.projection(center)-v);
		}
		return res;
	}
	Points intersection(Segment s){
		Points tmp = intersection(s.line());
		Points res;
		for(int i=0;i<tmp.size();i++){
			if(s.on(tmp[i]))res.pb(tmp[i]);
		}
		return res;
	}
	Points intersection(Circle c){
		Points res;
		double d = (c.center-center).norm();
		double a = acos((r*r+d*d-c.r*c.r)/(2.0*r*d));
		double t = (c.center-center).arg();
		res.pb(center+polar(r,t+a));
		res.pb(center+polar(r,t-a));
		return res;
	}
	Points tangent(Point p){
		Points res;
		double d = center.dist(p);
		double a = asin(r/d);
		double t = (center-p).arg();
		double len = sqrt(d*d-r*r);
		res.pb(p+polar(len,t+a));
		res.pb(p+polar(len,t-a));
		return res;
	}
	// verified CGL_7_G
	Points common_tangent(Circle c){
		Points res;
		int state = is_intersect(c);
		if(EQ(r,c.r)){ // radius of the two circles are same
			Point p = divide_rate(center,c.center,r,c.r);
			Vector v = (c.center-center).vert().normalize()*r;
			if(state==INCLUDE)return res;
			else if(state==INSCRIBED){
				cerr << "Same Circle" << endl;
				assert(false);	
			}else if(state==INTERSECT){
				res.pb(center+v);
				res.pb(center-v);
				return res;
			}else if(state==CIRCUMSCRIBED){
				res.pb(center+v);
				res.pb(center-v);
				res.pb(p);
				return res;
			}else{ // NOT_CROSS
				Points res = tangent(p);
				res.pb(center+v);
				res.pb(center-v);
				return res;
			}
		}else{
			Point p = divide_rate(center,c.center,r,c.r);
			Point q = divide_rate(center,c.center,r,-c.r);
			if(state==INCLUDE)return res;
			else if(state==INSCRIBED){
				res.pb(q);
				return res;	
			}else if(state==INTERSECT){
				return tangent(q);
			}else if(state==CIRCUMSCRIBED){
				res = tangent(q);
				res.pb(p);
				return res;
			}else{ // NOT_CROSS
				Points res = tangent(p);
				Points add = tangent(q);
				for(int i=0;i<add.size();i++)res.pb(add[i]);
				return res;
			}
		}	
	}
	// area of intersection between this circle
	// and left side of given line l.
	// "left" is defined by considering line as directed vector(l.a -> l.b) 
	// note: this function has not been verified yet.
	double left_area(Line l){
		Points res = intersection(l);
		if(res.size()<2){
			if(l.left(center))return M_PI*r*r;
			else return 0.0;
		}
		Vector a = res[0]-center;
		Vector b = res[1]-center;
		double tri = abs(a.area(b));
		double fan = r*r*abs(a.arg(b))/2.0;
		if(l.left(center))return M_PI*r*r-(fan-tri);
		else return fan-tri;
	}
	// returen signed area of intersection 
	// between triangle(center-a-b) and this circle
	// verified AOJ CGL_7_H
	double area_intersection_triangle(Point a,Point b){
		Segment s = Segment(a,b);
		double res = abs((a-center).area(b-center));
		if(EQ(res,0.0))return 0.0;
		if(in(a)&&!in(b)){
			Point p = intersection(s)[0];
			Point q = intersection(Segment(center,b))[0];
			res -= abs((p-b).area(q-b));
			res -= abs((p-center).area(q-center));
			res += abs(r*r*((p-center).angle(b-center))/2.0);
		}else if(!in(a)&&in(b)){
			Point p = intersection(s)[0];
			Point q = intersection(Segment(center,a))[0];
			res -= abs((p-a).area(q-a));
			res -= abs((p-center).area(q-center));
			res += abs(r*r*((p-center).angle(a-center))/2.0);
		}else if(!in(a)&&!in(b)){
			Points ps = intersection(s);
			if(ps.size()==2){
				Point p = ps[0];
				Point q = ps[1];
				Point m = divide_rate(p,q,1.0,1.0);
				res = abs(area_intersection_triangle(a,m))
					+ abs(area_intersection_triangle(m,b));
			}else{
				res = (r*r*(a-center).angle(b-center)/2.0);
			}
		}
		if((a-center).det(b-center)<0.0)res = -res;
		return res;
	}
	// area of intersection between given polygon and
	// this circle. polygon don't need to be convex 
	double area_intersection_polygon(Polygon pol){
		int n = pol.size();
		double res = 0.0;
		for(int i=0;i<n;i++){
			double tmp = area_intersection_triangle(pol[i],pol[(i+1)%n]);
			res += tmp;
		}
		return abs(res);
	}
};

// for input
Point input_point(){
	Point p;
	cin >> p.x >> p.y;
	return p;
}
Segment input_segment(){
	Point a,b;
	a = input_point();
	b = input_point();
	return Segment(a,b);
}
Line input_line(){
	Point a,b;
	a = input_point();
	b = input_point();
	return Line(a,b);
}
Circle input_circle(){
	Point c = input_point();
	double d;
	cin >> d;
	return Circle(c,d);
}



int main(){
	int n;
	double r;
	cin >> n >> r;
	Circle c = Circle(Point(0,0),r);
	Polygon pol;
	for(int i=0;i<n;i++){
		pol.pb(input_point());
	}
	printf("%.12f\n",c.area_intersection_polygon(pol));
	return 0;
}