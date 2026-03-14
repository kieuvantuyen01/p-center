#!/usr/bin/env python3
"""
Incremental SAT Solver for the Vertex P-Center Problem.

Uses PySAT with assumption literals to perform binary search on the
covering radius. The cardinality (at-most-p) encoding is added once;
coverage clauses are guarded by assumption variables and reactivated
per binary-search step.

Usage:
    python incremental_sat.py --input pmed1.txt --format pmed
    python incremental_sat.py --input u1060.tsp --format tsplib --p 10
"""

import argparse
import math
import sys
import time
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType


# ---------------------------------------------------------------
# Input parsers
# ---------------------------------------------------------------

def load_pmed(path: str) -> tuple[int, int, list[list[int]]]:
    """
    Load an OR-Library pmed instance.

    File format (Beasley, 1985):
        Line 1: n  m  p
        Next m lines: i  j  cost

    Returns (n, p, dist) where dist is the n×n shortest-path matrix.
    """
    with open(path) as f:
        lines = f.read().split('\n')

    tokens = lines[0].split()
    n, m, p = int(tokens[0]), int(tokens[1]), int(tokens[2])

    INF = 10**9
    dist = [[INF] * n for _ in range(n)]
    for i in range(n):
        dist[i][i] = 0

    for line_idx in range(1, m + 1):
        parts = lines[line_idx].split()
        u, v, w = int(parts[0]) - 1, int(parts[1]) - 1, int(parts[2])
        # Keep minimum cost for duplicate edges
        if w < dist[u][v]:
            dist[u][v] = w
            dist[v][u] = w

    # Floyd-Warshall
    for k in range(n):
        for i in range(n):
            if dist[i][k] == INF:
                continue
            for j in range(n):
                if dist[k][j] == INF:
                    continue
                new_d = dist[i][k] + dist[k][j]
                if new_d < dist[i][j]:
                    dist[i][j] = new_d

    return n, p, dist


def load_tsplib(path: str, p: int) -> tuple[int, int, list[list[int]]]:
    """
    Load a TSPLIB EUC_2D instance.

    Distances are Euclidean, rounded to nearest integer (TSPLIB convention).

    Returns (n, p, dist) where dist is the n×n distance matrix.
    """
    coords = []
    reading = False
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line == 'NODE_COORD_SECTION':
                reading = True
                continue
            if line in ('EOF', ''):
                if reading:
                    break
                continue
            if reading:
                parts = line.split()
                x = float(parts[1])
                y = float(parts[2])
                coords.append((x, y))

    n = len(coords)
    dist = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            dx = coords[i][0] - coords[j][0]
            dy = coords[i][1] - coords[j][1]
            d = int(round(math.sqrt(dx * dx + dy * dy)))
            dist[i][j] = d
            dist[j][i] = d

    return n, p, dist


# ---------------------------------------------------------------
# Incremental SAT solver
# ---------------------------------------------------------------

def solve_pcenter_incremental(
    dist: list[list[int]],
    n: int,
    p: int,
    solver_name: str = 'cadical195'
) -> tuple[int, list[int], dict]:
    """
    Solve the vertex p-center problem using incremental SAT.

    Parameters
    ----------
    dist : n×n distance matrix
    n    : number of vertices
    p    : number of centers
    solver_name : PySAT solver name

    Returns
    -------
    (optimal_radius, centers_list, stats_dict)
    """
    stats = {
        'n': n,
        'p': p,
        'solver': solver_name,
        'sat_calls': 0,
        'sat_results': [],
    }

    # ---- Step 1: Collect sorted unique distances ----
    dist_values = set()
    for i in range(n):
        for j in range(i + 1, n):
            dist_values.add(dist[i][j])
    D = sorted(dist_values)
    L = len(D)
    stats['num_distinct_distances'] = L

    # ---- Step 2: Precompute, for each distance threshold, which
    #      facilities can cover which clients ----
    # neighbors[i] = sorted list of (dist[i][j], j)
    neighbors = []
    for i in range(n):
        nb = []
        for j in range(n):
            if i != j:
                nb.append((dist[i][j], j))
            else:
                nb.append((0, j))
        nb.sort()
        neighbors.append(nb)

    # ---- Step 3: Initialize SAT solver (ONCE) ----
    solver = Solver(name=solver_name, bootstrap_with=[])

    # Variables: y_j for j = 0..n-1, use SAT var (j+1)
    # y_j = True  ⇒  vertex j is a center
    y_vars = list(range(1, n + 1))
    next_var = n + 1

    # ---- Step 4: Add at-most-p cardinality constraint (PERMANENT) ----
    atmost_clauses = CardEnc.atmost(
        lits=y_vars,
        bound=p,
        top_id=next_var - 1,
        encoding=EncType.seqcounter
    )
    for cl in atmost_clauses.clauses:
        solver.add_clause(cl)
    # Update next_var
    if atmost_clauses.clauses:
        next_var = atmost_clauses.nv + 1

    # ---- Step 5: Binary search on radius ----
    lo, hi = 0, L - 1
    best_centers = None
    best_radius = D[hi] if D else 0

    while lo < hi:
        mid = (lo + hi) // 2
        R = D[mid]

        # Create assumption literal
        alpha = next_var
        next_var += 1

        # Add guarded coverage clauses:
        #   ¬α ∨ y_{j1} ∨ y_{j2} ∨ ... for each client i
        for i in range(n):
            # Find all j such that dist[i][j] <= R
            covering = [-alpha]
            for d_ij, j in neighbors[i]:
                if d_ij <= R:
                    covering.append(y_vars[j])
                else:
                    break  # neighbors sorted by distance
            solver.add_clause(covering)

        # Solve with assumption [α]
        result = solver.solve(assumptions=[alpha])
        stats['sat_calls'] += 1
        stats['sat_results'].append(('SAT' if result else 'UNSAT', R))

        if result:
            hi = mid
            best_radius = R
            model = solver.get_model()
            best_centers = [j for j in range(n) if model[j] > 0]
        else:
            lo = mid + 1

    # Handle case lo == hi (not yet tested this exact radius)
    if best_centers is None and L > 0:
        R = D[lo]
        alpha = next_var
        next_var += 1
        for i in range(n):
            covering = [-alpha]
            for d_ij, j in neighbors[i]:
                if d_ij <= R:
                    covering.append(y_vars[j])
                else:
                    break
            solver.add_clause(covering)
        result = solver.solve(assumptions=[alpha])
        stats['sat_calls'] += 1
        stats['sat_results'].append(('SAT' if result else 'UNSAT', R))
        if result:
            best_radius = R
            model = solver.get_model()
            best_centers = [j for j in range(n) if model[j] > 0]

    solver.delete()

    return best_radius, best_centers, stats


# ---------------------------------------------------------------
# Verification
# ---------------------------------------------------------------

def verify_solution(dist, n, p, centers, radius):
    """Verify that the solution is valid."""
    if len(centers) > p:
        return False, f"Too many centers: {len(centers)} > {p}"

    for i in range(n):
        min_d = min(dist[i][j] for j in centers)
        if min_d > radius:
            return False, (
                f"Vertex {i} has min distance {min_d} to centers, "
                f"exceeds radius {radius}"
            )

    return True, "OK"


# ---------------------------------------------------------------
# Main
# ---------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description='Incremental SAT solver for the Vertex P-Center Problem'
    )
    parser.add_argument(
        '--input', '-i', required=True,
        help='Path to input file (pmed or TSPLIB format)'
    )
    parser.add_argument(
        '--format', '-f', choices=['pmed', 'tsplib'], default=None,
        help='Input format (auto-detect if not specified)'
    )
    parser.add_argument(
        '--p', type=int, default=None,
        help='Number of centers (required for TSPLIB, optional for pmed)'
    )
    parser.add_argument(
        '--solver', '-s', default='cadical195',
        choices=['cadical195', 'glucose4', 'minisat22', 'lingeling'],
        help='SAT solver to use (default: cadical195)'
    )
    args = parser.parse_args()

    # Auto-detect format
    fmt = args.format
    if fmt is None:
        if args.input.endswith('.tsp'):
            fmt = 'tsplib'
        else:
            fmt = 'pmed'

    # Load instance
    print(f"Loading instance: {args.input} (format: {fmt})")
    t0 = time.time()

    if fmt == 'pmed':
        n, p_file, dist = load_pmed(args.input)
        p = args.p if args.p is not None else p_file
    else:
        if args.p is None:
            print("Error: --p is required for TSPLIB format", file=sys.stderr)
            sys.exit(1)
        n, p, dist = load_tsplib(args.input, args.p)

    t_load = time.time() - t0
    print(f"  Loaded: n={n}, p={p} ({t_load:.2f}s)")

    # Solve
    print(f"\nSolving with Incremental SAT (solver={args.solver})...")
    t1 = time.time()
    radius, centers, stats = solve_pcenter_incremental(dist, n, p, args.solver)
    t_solve = time.time() - t1

    # Output results
    print(f"\n{'='*60}")
    print(f"  RESULT")
    print(f"{'='*60}")
    print(f"  Optimal radius:  {radius}")
    print(f"  Centers ({len(centers)}):    {[c+1 for c in centers]}")
    print(f"  SAT calls:       {stats['sat_calls']}")
    print(f"  Distinct dists:  {stats['num_distinct_distances']}")
    print(f"  Solve time:      {t_solve:.3f}s")
    print(f"  Total time:      {time.time()-t0:.3f}s")

    # Verify
    valid, msg = verify_solution(dist, n, p, centers, radius)
    print(f"  Verification:    {'✓ PASS' if valid else '✗ FAIL: ' + msg}")

    # Print SAT call log
    print(f"\n  Binary search log:")
    for i, (res, r) in enumerate(stats['sat_results']):
        print(f"    Step {i+1}: R={r} → {res}")

    print(f"{'='*60}")


if __name__ == '__main__':
    main()
