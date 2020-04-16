/*
Tom Krobatsch
CS302
Lab 04
03-19-18
*/

// include header files needed
#include <cstdlib> //exit
#include <iomanip> //setw and left
#include <fstream> //file stuff
#include <ostream> //file stuff
#include <iostream>
#include <sstream>
#include <vector>
#include <string>
//#include <getopt.h>
#include "getopt.h"
#include <cmath>
#include <map>
#include <algorithm>
#include <iomanip>
#include <utility>
#include <queue>
#include <stack>
#include <climits>
#include <string.h>
#include <limits>

extern const char ETX = 0x3;


using namespace std;

class city {
public:
	city() {
		name = "";
		type = "";
		zone = 0;
		population = 0;
		latitude = 0;
		longitude = 0;
	}
	//get variables
	string get_name() const { return name; }
	string get_type() const { return type; }
	int get_zone() const { return zone; }
	int get_pop() const { return population; }
	float get_lat() const { return latitude; }
	float get_long() const { return longitude; }
	//overloaded operators
	friend istream& operator>> (istream& in, city& cty) {
		in >> cty.zone >> cty.name >> cty.type >> cty.latitude >> cty.longitude >> cty.population;
		return in;
	}
	friend ostream& operator<< (ostream& out, const city& cty) {
		out << left << setw(20) << cty.name;
		out << left << setw(12) << cty.type;
		out << left << setw(2) << cty.zone;
		out << right << setw(10) << cty.population;
		out << setprecision(2) << fixed;
		out << right << setw(8) << cty.latitude;
		out << right << setw(8) << cty.longitude;
		return out;
	}
	friend bool operator==(const city &lhs, const city &rhs) {
		return(lhs.get_name() == rhs.get_name());
	}
	friend bool operator<(const city &lhs, const city &rhs) {
		return(lhs.get_name() < rhs.get_name());
	}
	friend bool operator>(const city &lhs, const city &rhs) {
		return(lhs.get_name() > rhs.get_name());
	}
private:
	string name, type;
	int zone, population;
	float latitude, longitude;
};

class dtable {
public:
	dtable(int i) { buf = new float[(i*(i + 1)) / 2]; }
	~dtable() { delete[] buf; }
	float* operator[](int i) { return &buf[(i*(i + 1)) / 2]; }
	float operator()(int i, int j) {
		int index;
		if (i < j)
			index = ((j*(j + 1)) / 2) + i;
		else
			index = ((i*(i + 1)) / 2) + j;
		return buf[index];
	}
	float calc(float sig1, float lamb1, float sig2, float lamb2) {
		sig1 = sig1 * (M_PI / 180);
		lamb1 = lamb1 * (M_PI / 180);
		sig2 = sig2 * (M_PI / 180);
		lamb2 = lamb2 * (M_PI / 180);
		float distance;
		float sigma;
		sigma = acos(sin(sig1)*sin(sig2) + cos(sig1)*cos(sig2)*cos(abs(lamb1 - lamb2)));
		distance = 3982 * sigma;
		return (5.0*round(distance / 5.0));
	}

private:
	float * buf;
};

class edgelist {
public:
	edgelist(int i) { buf = new int[(i*(i + 1)) / 2]; }
	~edgelist() { delete[] buf; }
	int* operator[](int i) { return &buf[(i*(i + 1)) / 2]; }
	int operator()(int i, int j) {
		int index;
		if (i < j)
			index = ((j*(j + 1)) / 2) + i;
		else
			index = ((i*(i + 1)) / 2) + j;
		return buf[index];
	}
private:
	int * buf;
};


template <typename Tkey, typename Twgt>
class graph {
public:
	graph() {}
	void read(vector<city> &city_data, dtable &dist, edgelist &adj_matrix);
	int get_Vert_count() { return (int)V.size(); }
	Tkey operator[](int i) { return V[i]; }
	int get_edge(int i, int j) { return E[i][j]; }
	int get_edge_size(int i) { return E[i].size(); }
	Twgt get_weight(int i, int j) { return W[i][j]; }
	void bfs_route(int, int);
	void dijkstra_route(int, int);
	void show_route(int, int, bool);
private:
	vector< Tkey > V;         // vertex list
	vector< vector<int> > E;  // edge matrix
	vector< vector<Twgt> > W; // weight matrix
	map<Tkey, int> key_map;    // key-to-index map
	vector<Twgt> vdist;
	vector<int> vlink;
	typedef enum { WHITE, BLACK } vcolor_t;
	vector<vcolor_t> vcolor;
};

template <typename Tkey, typename Twgt>
void graph<Tkey, Twgt>::read(vector<city> &city_data, dtable &dist, edgelist &adj_matrix) {
	vector< pair<int, int> > Eij;
	vector< Twgt > Wij;

	for (int i = 0; i < (int)city_data.size(); i++) {
		key_map.insert(make_pair(city_data[i], i));
		for (int j = 0; j < (int)city_data.size(); j++) {
			if (adj_matrix(i, j) == 1) {
				Eij.push_back(make_pair(i, j));
				Wij.push_back(dist(i, j));
			}
		}
	}

	// Create vertex list and edge matrix
	V.resize(key_map.size());
	E.resize(key_map.size());
	W.resize(key_map.size());
	typename map<Tkey, int>::iterator kmp;
	vector< map<int, Twgt> > EW;
	EW.resize(key_map.size());
	for (int k = 0; k < (int)Eij.size(); k++) {
		int i = Eij[k].first;
		int j = Eij[k].second;
		Twgt w = Wij[k];
		EW[i].insert(make_pair(j, w));
		EW[j].insert(make_pair(i, w));
	}
	typename map<int, Twgt>::iterator p;
	for (int i = 0; i < (int)EW.size(); i++) {
		for (p = EW[i].begin(); p != EW[i].end(); ++p) {
			E[i].push_back(p->first);
			W[i].push_back(p->second);
		}
	}
	for (kmp = key_map.begin(); kmp != key_map.end(); ++kmp)
		V[kmp->second] = kmp->first;
}

template <typename Tkey, typename Twgt>
void graph<Tkey, Twgt>::bfs_route(int source, int sink) {
	vdist.assign(V.size(), numeric_limits<Twgt>::max());
	vdist[source] = 0;
	vlink.assign(V.size(), -1);
	vlink[source] = source;
	queue<int> Q;
	Q.push(source);
	while (!Q.empty()) {
		int i = Q.front();
		Q.pop();
		if (i == sink)
			break;
		for (int k = 0; k < (int)E[i].size(); k++) {
			int j = E[i][k];
			Twgt wij = W[i][k];
			if (vdist[j] == numeric_limits<Twgt>::max()) {
				vdist[j] = vdist[i] + wij;
				vlink[j] = i;
				Q.push(j);
			}
		}
	}
	while (!Q.empty())
		Q.pop();
}

template <typename Tkey, typename Twgt>
void graph<Tkey, Twgt>::dijkstra_route(int source, int sink) {
	vcolor.assign(V.size(), WHITE);
	vdist.assign(V.size(), numeric_limits<Twgt>::max());
	vdist[source] = 0;
	vlink.assign(V.size(), -1);
	vlink[source] = source;
	while (1) {
		int i;
		int i_mindist = -1;
		Twgt mindist = numeric_limits<Twgt>::max();
		for (int i = 0; i < (int)vcolor.size(); i++) {
			if (vcolor[i] == WHITE && mindist > vdist[i]) {
				i_mindist = i;
				mindist = vdist[i];
			}
		}
		if ((i = i_mindist) == -1)
			return;
		vcolor[i] = BLACK;
		if (i == sink)
			break;

		for (int k = 0; k < (int)E[i].size(); k++) {
			int j = E[i][k];
			Twgt wij = W[i][k];
			if (vcolor[j] == WHITE) {
				if (vdist[j] > vdist[i] + wij) {
					vdist[j] = vdist[i] + wij;
					vlink[j] = i;
				}
			}
		}
	}
}

template <typename Tkey, typename Twgt>
void graph<Tkey, Twgt>::show_route(int source, int sink, bool show) {
	if (vdist[sink] == INT_MAX) {
		cout << "No path from " << V[source]
			<< " to " << V[sink] << "\n";
		return;
	}
	stack<int> S;
	for (int i = sink; i != source; i = vlink[i])
		S.push(i);
	S.push(source);

	if (!show) {
		int i = S.top();
		S.pop();
		int j;
		while (!S.empty()) {
			j = S.top();
			S.pop();
		}
		cout << setw(2) << i << " " << V[i].get_name();
		cout << " to" << setw(3) << j << " " << V[j].get_name();
		cout << " : " << setw(4) << right << vdist[j] << " miles" << endl;
	}

	if (show) {
		Twgt prev;
		while (!S.empty()) {
			int i = S.top();
			S.pop();
			cout << setw(8) << right << vdist[i] << " miles :";
			cout << setw(3) << i << " ";
			cout << setw(23) << left << V[i].get_name();
			if (vdist[i] != 0) {
				cout << setw(5) << right << vdist[i] - prev << " miles";
			}
			cout << endl;
			prev = vdist[i];
		}
	}
}

void create_citygraph(vector<city> &city_data, dtable &dist, edgelist &adj_matrix) {
	//create edges based on rules
	for (int i = 0; i < (int)city_data.size(); i++) {
		map<float, int> rg_map;
		map<int, map<float, int> > zd_map;
		map<int, map<float, int> >::iterator it;
		for (int j = 0; j < (int)city_data.size(); j++) {
			if (i != j) {
				//regional to other regional cities in the same zone
				if ((city_data[i].get_zone() == city_data[j].get_zone()) &&
					(city_data[i].get_type() == "REGIONAL") &&
					(city_data[j].get_type() == "REGIONAL")) {
					if (i < j)
						adj_matrix[j][i] = 1;
					else
						adj_matrix[i][j] = 1;
				}
				//gateway cities in the same zone
				if ((city_data[i].get_zone() == city_data[j].get_zone()) &&
					(city_data[i].get_type() == "GATEWAY") &&
					(city_data[j].get_type() == "GATEWAY")) {
					if (i < j)
						adj_matrix[j][i] = 1;
					else
						adj_matrix[i][j] = 1;
				}
				//regional to gateway in the same zone
				if ((city_data[i].get_zone() == city_data[j].get_zone()) &&
					(city_data[i].get_type() == "REGIONAL") &&
					(city_data[j].get_type() == "GATEWAY"))
					//add to map keyed off dist
					rg_map[dist(i, j)] = j;
				//gateway cities in other zones
				if ((city_data[i].get_zone() != city_data[j].get_zone()) &&
					(city_data[i].get_type() == "GATEWAY") &&
					(city_data[j].get_type() == "GATEWAY") &&
					(dist(i, j) < 6000))
					//add to map keyed off zone/dist
					zd_map[city_data[j].get_zone()][dist(i, j)] = j;
			}
		}
		//selecting first in map for smallest dist
		if ((int)rg_map.size() > 0) {
			if (i < rg_map.begin()->second)
				adj_matrix[rg_map.begin()->second][i] = 1;
			else
				adj_matrix[i][rg_map.begin()->second] = 1;
		}
		//selecting first in nested map for smallest dist by zone
		for (it = zd_map.begin(); it != zd_map.end(); it++) {
			if (i < it->second.begin()->second)
				adj_matrix[it->second.begin()->second][i] = 1;
			else
				adj_matrix[i][it->second.begin()->second] = 1;
		}
	}
}

void read_cityinfo(vector<city> &city_data, map<string, int> &city_map) {
	ifstream fin;
	//open file, error catch opening and read in
	fin.open("citylist.txt");
	if (!fin) {
		cerr << "Error opening file. Check if file exists." << endl;
		exit(0);
	}
	string data;
	while (getline(fin, data)) {
		if ((data != "") && (data[0] != '#')) {
			city temp;
			stringstream in;
			in << data;
			in >> temp;
			city_data.push_back(temp);
		}
	}
	fin.close();

	//fill city keymap
	for (int i = 0; i < (int)city_data.size(); i++) {
		city_map[city_data[i].get_name()] = i;
	}
}

void write_cityinfo(graph <city, float> &city_graph) {
	//open file with error check
	ofstream fout;
	fout.open("cityinfo.txt");
	if (!fout) {
		cerr << "Error creating file. Make sure you have write permission." << endl;
		exit(0);
	}
	fout << "CITY INFO (N=" << city_graph.get_Vert_count() << "):" << endl << endl;
	//write and close file
	for (int i = 0; i < (int)city_graph.get_Vert_count(); i++)
		fout << " " << right << setw(2) << i << " " << city_graph[i] << endl;
	fout.close();
}

void write_citydtable(graph <city, float> &city_graph, dtable &dist, int width) {
	//open file with error check
	ofstream fout;
	fout.open("citydtable.txt");
	if (!fout) {
		cerr << "Error creating file. Make sure you have write permission." << endl;
		exit(0);
	}
	fout << "DISTANCE TABLE:" << endl << endl;
	// write and close file
	for (int i = 1; i < (int)city_graph.get_Vert_count(); i++) {
		for (int j = 0; j < i; j++) {
			if (i != j) {
				fout << " " << right << setfill(' ') << setw(2) << i << " ";
				fout << left << setfill('.') << setw(width) << city_graph[i].get_name() + " to " + city_graph[j].get_name() + " ";
				fout << right << setfill(' ') << setw(5) << dist(i, j) << " miles" << endl;
			}
		}
		fout << endl;
	}
	fout.close();
}

void write_citygraph(graph <city, float> &city_graph) {
	//open file with error check
	ofstream fout;
	fout.open("citygraph.txt");
	if (!fout) {
		cerr << "Error creating file. Make sure you have write permission." << endl;
		exit(0);
	}
	fout << "CITY GRAPH:" << endl << endl;
	// write and close file
	for (int i = 0; i < city_graph.get_Vert_count(); i++) {
		fout << " " << right << setw(2) << i << " ";
		fout << city_graph[i].get_name() << endl;
		for (int j = 0; j < (int)city_graph.get_edge_size(i); j++) {
			//for (int j = 0; j < (int)city_graph.E[i].size(); j++) {
				//int k = city_graph.E[i][j];
			int k = city_graph.get_edge(i, j);
			fout << right << setw(6) << k << " " << city_graph[k].get_name() + ": ";
			//fout << city_graph.W[i][j] << " miles" << endl;
			fout << city_graph.get_weight(i, j) << " miles" << endl;
		}
		if (i != (int)city_graph.get_Vert_count() - 1)
			fout << endl;
	}
	fout.close();
}

int main(int argc, char **argv)
{
	//option decoding using getopt
	bool option_write_cityinfo = false, option_write_citydtable = false, option_write_citygraph = false;
	bool option_mode_bfs = false, option_mode_dijkstra = false, option_mode_show = false;
	int c;

	while (1) {
		static struct option long_options[] = {
		{ "write_info",no_argument,0,'a' },
		{ "write_dtable",no_argument,0,'b' },
		{ "write_graph",no_argument,0,'c' },
		{ "mode_bfs",no_argument,0,'d' },
		{ "mode_dijkstra",no_argument,0,'e' },
		{ "show",no_argument,0,'f' },
		{0,0,0,0}
		};

		int option_index = 0;
		c = getopt_long_only(argc, argv, "abcdef", long_options, &option_index);

		if (c == -1)
			break;

		switch (c) {
		case 0:
			break;

		case 1:
			//error message
			cout << "usage: ./Citysim [-write_info] [-write_dtable] [-write_graph] ";
			cout << "[-mode_bfs|mode_dijkstra [-randomseed][-show]]" << endl;
			exit(1);
			break;

		case 'a':
			option_write_cityinfo = true;
			break;

		case 'b':
			option_write_citydtable = true;
			break;

		case 'c':
			option_write_citygraph = true;
			break;

		case 'd':
			option_mode_bfs = true;
			break;

		case 'e':
			option_mode_dijkstra = true;
			break;

		case 'f':
			option_mode_show = true;
			break;

		case '?':
			//error message
			cout << "usage: ./Citysim [-write_info] [-write_dtable] [-write_graph] ";
			cout << "[-mode_bfs|mode_dijkstra [-show]]" << endl;
			exit(1);
			break;
		default:
			cout << "default" << endl;
			exit(1);
		}
	}

	//catch if user enter any non option arguments and exit
	if (optind != argc) {
		cout << "usage: ./Citysim [-write_info] [-write_dtable] [-write_graph] ";
		cout << "[-mode_bfs|mode_dijkstra [-show]]" << endl;
		cerr << "Entered non-option argument" << endl;
		exit(1);
	}
	//catch for both bfs and dijkstra mode
	if (option_mode_bfs == true and option_mode_dijkstra == true) {
		cout << "usage: ./Citysim [-write_info] [-write_dtable] [-write_graph] ";
		cout << "[-mode_bfs|mode_dijkstra [-show]]" << endl;
		cerr << "Select either -mode_bfs or -mode_dijkstra" << endl;
		exit(1);
	}
	//user entered show without mode
	if (option_mode_bfs == false and option_mode_dijkstra == false and option_mode_show == true) {
		cout << "usage: ./Citysim [-write_info] [-write_dtable] [-write_graph] ";
		cout << "[-mode_bfs|mode_dijkstra [-show]]" << endl;
		cerr << "Select either -mode_bfs or -mode_dijkstra with -show option" << endl;
		exit(1);
	}



	//create city object and fill
	vector<city> city_data;
	map<string, int> city_map;
	read_cityinfo(city_data, city_map);
	//get width of longest city name
	int name_width = 0;
	for (int i = 0; i < (int)city_data.size(); i++) {
		if ((int)city_data[i].get_name().size() > name_width)
			name_width = city_data[i].get_name().size();
	}
	//create dist table and fill
	dtable dist((int)city_data.size());
	for (int i = 0; i < (int)city_data.size(); i++) {
		for (int j = 0; j < (int)city_data.size(); j++) {
			float calc = dist.calc(city_data[i].get_lat(), city_data[i].get_long(), city_data[j].get_lat(), city_data[j].get_long());
			if (i < j)
				dist[j][i] = calc;
			else
				dist[i][j] = calc;
		}
	}
	//create edge list and initlize to 0
	edgelist adj_matrix((int)city_data.size());
	for (int i = 0; i < (int)city_data.size(); i++) {
		for (int j = 0; j < (int)city_data.size(); j++) {
			adj_matrix[i][j] = 0;
		}
	}
	//fill edge list
	create_citygraph(city_data, dist, adj_matrix);
	//create graph
	graph <city, float> city_graph;
	city_graph.read(city_data, dist, adj_matrix);

	//all file handling
	if (option_write_cityinfo)
		write_cityinfo(city_graph);
	if (option_write_citydtable)
		write_citydtable(city_graph, dist, 2 * name_width + 4);
	if (option_write_citygraph)
		write_citygraph(city_graph);

	if (option_mode_bfs or option_mode_dijkstra) {
		string read;
		bool pass1 = false;
		bool pass2 = false;
		int count = 0;
		string str1, str2;
		cout << "Enter> ";
		while (getline(cin, read)) {
			map<string, int>::iterator it1, it2;
			stringstream ss;
			ss << read;
			//count number of "words" read
			if ((count == 0) and (ss >> str1))
				count = 1;
			if (count == 1) {
				if (ss >> str2)
					count = 2;
			}
			//assign pointers by search
			it1 = city_map.upper_bound(str1);
			it2 = city_map.upper_bound(str2);
			// if you have two words process errors and run search
			if (count == 2) {
				if (it1 == city_map.end()) {
					pass1 = false;
					cerr << str1 << " unknown" << endl;
				}
				else if (it1->first[0] != str1[0]) {
					pass1 = false;
					cerr << str1 << " unknown" << endl;
				}
				else
					pass1 = true;

				if (it2 == city_map.end()) {
					pass2 = false;
					cerr << str2 << " unknown" << endl;
				}
				else if (it2->first[0] != str2[0]) {
					pass2 = false;
					cerr << str2 << " unknown" << endl;
				}
				else
					pass2 = true;
				//if both cities are found and valid run method
				if (pass1 and pass2) {
					if (option_mode_bfs)
						city_graph.bfs_route(it1->second, it2->second);
					if (option_mode_dijkstra)
						city_graph.dijkstra_route(it1->second, it2->second);
					city_graph.show_route(it1->second, it2->second, option_mode_show);
				}
				cout << endl << "Enter> ";
				//reset varibles
				count = 0;
				str1.clear();
				str2.clear();
			}
		}
		cout << endl;
	}
}

