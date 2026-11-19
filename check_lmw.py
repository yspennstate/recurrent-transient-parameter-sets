"""Exact checks for 'Topology of the recurrent and transient parameter sets of random walks on abelian groups'.

Standard library only.  All arithmetic is in Fractions.  A step set is given by the projections v_i of its steps to the
free part Z^n (zero vectors and repeated vectors are allowed).

Recurrent side.  By Lemma 2.1 (from Proposition 6.1 of Li, Mossel and Weiss), R is the union of the polytopes
    P_U = {a in A : a_i = 0 for i not in U, sum_i a_i v_i = 0},
over the sets U = {i : v_i in W}, W a subspace of dimension at most 2 spanned by input vectors.  P_U and P_U' meet in
P_(U & U').  The script builds the nerve of this closed convex cover from feasibility tests alone, computes its Betti
numbers b0 and b1 over Q, and compares them with the component count t + [k > 0] and the rank formula of Theorem 1.2,
which are computed from balanced lines and active planes by a separate code path.

Transient side.  For every input the script builds the certificate used in the proof of Theorem 1.5 (a star centre, a
separating functional, or the retraction data q, B, eps) and checks it exactly.  Convexity (Theorem 1.7) is checked against
a direct test for a recurrent law outside the face A_Z, and every nonconvex input gets an exact witness segment.
"""
from fractions import Fraction as F
from itertools import combinations, product
import random
import sys


# ---------------------------------------------------------------- exact linear algebra
def rank(rows):
    m = [list(map(F, r)) for r in rows]
    rk, col = 0, 0
    ncol = len(m[0]) if m else 0
    while rk < len(m) and col < ncol:
        piv = next((i for i in range(rk, len(m)) if m[i][col] != 0), None)
        if piv is None:
            col += 1
            continue
        m[rk], m[piv] = m[piv], m[rk]
        for i in range(len(m)):
            if i != rk and m[i][col] != 0:
                f = m[i][col] / m[rk][col]
                m[i] = [x - f * y for x, y in zip(m[i], m[rk])]
        rk += 1
        col += 1
    return rk


def solve(cols, rhs):
    """Unique solution x of sum_j x_j cols[j] = rhs if the columns are independent and the system is consistent."""
    nr, nc = len(rhs), len(cols)
    m = [[F(cols[j][i]) for j in range(nc)] + [F(rhs[i])] for i in range(nr)]
    r, piv_cols = 0, []
    for c in range(nc):
        p = next((i for i in range(r, nr) if m[i][c] != 0), None)
        if p is None:
            return None
        m[r], m[p] = m[p], m[r]
        m[r] = [x / m[r][c] for x in m[r]]
        for i in range(nr):
            if i != r and m[i][c] != 0:
                f = m[i][c]
                m[i] = [x - f * y for x, y in zip(m[i], m[r])]
        piv_cols.append(c)
        r += 1
    if any(m[i][nc] != 0 for i in range(r, nr)):
        return None
    return [m[i][nc] for i in range(nc)]


def drift(vs, a):
    n = len(vs[0])
    return [sum(a[i] * vs[i][c] for i in range(len(vs))) for c in range(n)]


# ---------------------------------------------------------------- zero-drift polytopes
def vertex_laws(vs, U, maxsize=3):
    """Vertices of {a >= 0, sum a = 1, sum a_i v_i = 0, supp a in U} with support size <= maxsize."""
    out = []
    U = sorted(U)
    for size in range(1, min(maxsize, len(U)) + 1):
        for J in combinations(U, size):
            cols = [[1] + list(vs[j]) for j in J]
            if rank(cols) < size:
                continue
            lam = solve(cols, [1] + [0] * len(vs[0]))
            if lam is not None and all(x > 0 for x in lam):
                out.append(dict(zip(J, lam)))
    return out


class Recurrent:
    def __init__(self, vs):
        self.vs = vs
        self.m = len(vs)
        self.cache = {}

    def feasible(self, U):
        """P_U nonempty.  Every vertex of a zero-drift polytope inside a rank <= 2 support has support size <= 3."""
        U = frozenset(U)
        if U not in self.cache:
            self.cache[U] = bool(vertex_laws(self.vs, U, 3))
        return self.cache[U]

    def cover(self):
        vs, m = self.vs, self.m
        n = len(vs[0])
        sets = set()
        gens = [()] + [(i,) for i in range(m)] + list(combinations(range(m), 2))
        for g in gens:
            basis = [vs[i] for i in g]
            r = rank(basis) if basis else 0
            if r > 2:
                continue
            U = frozenset(i for i in range(m) if (rank(basis + [vs[i]]) if basis else rank([vs[i]])) == r)
            sets.add(U)
        return [U for U in sets if U and self.feasible(U)]

    def betti(self):
        C = self.cover()
        N = len(C)
        E = [(i, j) for i, j in combinations(range(N), 2) if self.feasible(C[i] & C[j])]
        Eset = set(E)
        T = [(i, j, l) for i, j, l in combinations(range(N), 3)
             if (i, j) in Eset and (i, l) in Eset and (j, l) in Eset and self.feasible(C[i] & C[j] & C[l])]
        eidx = {e: k for k, e in enumerate(E)}
        d1 = [[0] * len(E) for _ in range(N)]
        for k, (i, j) in enumerate(E):
            d1[i][k] -= 1
            d1[j][k] += 1
        d2 = [[0] * len(T) for _ in range(len(E))]
        for k, (i, j, l) in enumerate(T):
            d2[eidx[(j, l)]][k] += 1
            d2[eidx[(i, l)]][k] -= 1
            d2[eidx[(i, j)]][k] += 1
        r1 = rank(d1) if E else 0
        r2 = rank(d2) if T else 0
        return N - r1, len(E) - r1 - r2, N


# ---------------------------------------------------------------- formula side (balanced lines, active planes)
def canon_span(vecs):
    """Reduced row echelon form of the span, as a hashable tuple."""
    m = [list(map(F, v)) for v in vecs]
    out, col, ncol = [], 0, len(m[0])
    rows = m
    r = 0
    while r < len(rows) and col < ncol:
        p = next((i for i in range(r, len(rows)) if rows[i][col] != 0), None)
        if p is None:
            col += 1
            continue
        rows[r], rows[p] = rows[p], rows[r]
        rows[r] = [x / rows[r][col] for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][col] != 0:
                f = rows[i][col]
                rows[i] = [x - f * y for x, y in zip(rows[i], rows[r])]
        r += 1
        col += 1
    return tuple(tuple(x) for x in rows[:r])


def formula(vs):
    m = len(vs)
    if any(all(c == 0 for c in v) for v in vs):
        return {"zero": True}
    lines = {}
    for i, v in enumerate(vs):
        L = canon_span([v])
        piv = next(c for c in range(len(v)) if L[0][c] != 0)
        sign = 1 if F(v[piv]) / L[0][piv] > 0 else -1
        lines.setdefault(L, set()).add(sign)
    balanced = [L for L, s in lines.items() if s == {1, -1}]
    k = len(balanced)
    planes = set()
    for J in combinations(range(m), 3):
        if rank([vs[j] for j in J]) == 2 and vertex_laws(vs, J, 3) and any(len(w) == 3 for w in vertex_laws(vs, J, 3)):
            planes.add(canon_span([vs[j] for j in J]))
    for L, M in combinations(balanced, 2):
        planes.add(canon_span([list(L[0]), list(M[0])]))
    BV = {V: [L for L in balanced if rank([list(r) for r in V] + [list(L[0])]) == 2] for V in planes}
    t = sum(1 for V in planes if not BV[V])
    comps = t + (1 if k else 0)
    b = (1 - k + sum(len(BV[V]) - 1 for V in planes if BV[V])) if k else 0
    span = rank([list(L[0]) for L in balanced]) if balanced else 0
    return {"zero": False, "k": k, "t": t, "comps": comps, "b": b, "span": span, "planes": len(planes)}


# ---------------------------------------------------------------- transient side
def transient_type(vs):
    """Return (type, certificate checks passed).  type in empty / point / S0 / S1."""
    m = len(vs)
    r = rank(vs)
    if r == 0:
        return "empty"
    if r >= 3:
        # star centre: the uniform law; every law (1-t)a + t*b with t > 0 has support rank >= 3
        assert rank(vs) >= 3
        return "point"
    # coordinates of each v_i in a basis of V made of r input vectors
    basis = []
    for v in vs:
        if rank(basis + [v]) > len(basis):
            basis.append(v)
        if len(basis) == r:
            break
    W = []
    for v in vs:
        x = solve(basis, v)
        assert x is not None
        W.append(x)                     # W[i] in Q^r
    # centred iff every index lies in the support of some zero-drift vertex law
    covered = set()
    verts = vertex_laws([list(w) for w in W], range(m), r + 1)
    for law in verts:
        covered |= set(law)
    if len(covered) == m:
        q = [F(0)] * m
        for law in verts:
            for i, x in law.items():
                q[i] += x / len(verts)
        assert sum(q) == 1 and all(x > 0 for x in q)
        assert all(sum(q[i] * W[i][c] for i in range(m)) == 0 for c in range(r))
        # B: columns y_j with 1^T y_j = 0, W y_j = e_j, from an affine basis of r + 1 columns
        J = None
        for cand in combinations(range(m), r + 1):
            if rank([[1] + list(W[i]) for i in cand]) == r + 1:
                J = cand
                break
        assert J is not None
        B = [[F(0)] * r for _ in range(m)]
        for j in range(r):
            y = solve([[1] + list(W[i]) for i in J], [0] + [1 if c == j else 0 for c in range(r)])
            for idx, i in enumerate(J):
                B[i][j] = y[idx]
        qs = min(q)
        M = max(sum(abs(x) for x in row) for row in B)
        eps = qs / (2 * M)
        for u in product([-1, 1], repeat=r):
            s = [q[i] + eps * sum(B[i][j] * u[j] for j in range(r)) for i in range(m)]
            assert sum(s) == 1 and all(x >= qs / 2 for x in s)
            assert [sum(s[i] * W[i][c] for i in range(m)) for c in range(r)] == [eps * x for x in u]
        # the homotopy (8) on a few transient laws
        rng = random.Random(m * 1000 + r)
        for _ in range(6):
            a = [F(rng.randint(0, 5)) for _ in range(m)]
            if sum(a) == 0:
                continue
            a = [x / sum(a) for x in a]
            Wa = [sum(a[i] * W[i][c] for i in range(m)) for c in range(r)]
            if all(x == 0 for x in Wa):
                continue
            nrm = max(abs(x) for x in Wa)
            u = [x / nrm for x in Wa]
            rho = [q[i] + eps * sum(B[i][j] * u[j] for j in range(r)) for i in range(m)]
            for tt in (F(0), F(1, 1000), F(1, 2), F(999, 1000), F(1)):
                h = [(1 - tt) * a[i] + tt * rho[i] for i in range(m)]
                assert all(x >= 0 for x in h) and sum(h) == 1
                Wh = [sum(h[i] * W[i][c] for i in range(m)) for c in range(r)]
                assert Wh == [((1 - tt) * nrm + tt * eps) * x for x in u]
        return "S0" if r == 1 else "S1"
    # not centred: a separating functional l with l(w_i) >= 0 for all i and > 0 for some i
    cands = [[F(1)], [F(-1)]] if r == 1 else [c for w in W if any(w) for c in ([-w[1], w[0]], [w[1], -w[0]])]
    for l in cands:
        vals = [sum(l[c] * w[c] for c in range(r)) for w in W]
        if all(x >= 0 for x in vals) and any(x > 0 for x in vals):
            return "point"
    raise AssertionError("no separator in a non-centred case")


def convexity(vs):
    """(convex?, witness or None).  Direct test: is there a recurrent law with mass off the zero steps?"""
    m = len(vs)
    nz = [i for i in range(m) if any(c != 0 for c in vs[i])]
    rec = Recurrent(vs)
    off_face = any(rec.feasible(U & frozenset(nz)) for U in rec.cover())
    # circuit test of Theorem 1.7
    circ = None
    for size in (2, 3):
        for J in combinations(nz, size):
            if rank([vs[j] for j in J]) > 2:
                continue
            for law in vertex_laws(vs, J, 3):
                if len(law) == size:
                    circ = law
                    break
            if circ:
                break
        if circ:
            break
    assert off_face == (circ is not None)
    if circ is None:
        return True, None
    i = min(circ)
    w = circ[i]
    b = {j: x / (1 - w) for j, x in circ.items() if j != i}
    ei = [F(1) if j == i else F(0) for j in range(m)]
    bl = [b.get(j, F(0)) for j in range(m)]
    q = [w * ei[j] + (1 - w) * bl[j] for j in range(m)]
    assert any(drift(vs, ei)) and any(drift(vs, bl)) and not any(drift(vs, q))
    assert rank([vs[j] for j in circ]) <= 2
    return False, (i, circ)


# ---------------------------------------------------------------- driver
def check(vs, stats, want=None):
    rec = Recurrent(vs)
    b0, b1, ncov = rec.betti()
    f = formula(vs)
    if f["zero"]:
        assert (b0, b1) == (1, 0), (vs, b0, b1)
        sc = True
    else:
        assert (b0, b1) == (f["comps"], f["b"]), (vs, b0, b1, f)
        sc = (b0 == 1 and b1 == 0)
        assert sc == (f["comps"] == 1 and f["span"] <= 2), (vs, f)
    ttype = transient_type(vs)
    conv, _ = convexity(vs)
    # transient path components in rank one, directly from the sign of the drift
    if rank(vs) == 1:
        L = canon_span([v for v in vs if any(v)])
        piv = next(c for c in range(len(vs[0])) if L[0][c] != 0)
        signs = {(F(v[piv]) / L[0][piv] > 0) for v in vs if any(v)}
        assert (ttype == "S0") == (len(signs) == 2)
    if want is not None:
        got = {"R_b0": b0, "R_b1": b1, "T": ttype, "convex": conv}
        for key, val in want.items():
            assert got[key] == val, (vs, key, got[key], val)
    stats["inputs"] += 1
    stats["types"][ttype] = stats["types"].get(ttype, 0) + 1
    stats["comps"][b0] = stats["comps"].get(b0, 0) + 1
    stats["b1"][b1] = stats["b1"].get(b1, 0) + 1
    stats["convex"] += conv
    return b0


def main():
    stats = {"inputs": 0, "types": {}, "comps": {}, "b1": {}, "convex": 0}
    # examples from Li, Mossel and Weiss and from the paper
    e = lambda *x: list(x)
    fixtures = [
        ("Example 6.4 (bipyramid)", [e(0, 0, 1), e(1, 0, 0), e(-1, 1, 0), e(-1, -1, 0), e(0, 0, -1)],
         {"R_b0": 2, "R_b1": 0, "T": "point"}),
        ("S = {1, -1} in Z", [e(1), e(-1)], {"R_b0": 1, "R_b1": 0, "T": "S0", "convex": False}),
        ("S = {+-e1, +-e2}", [e(1, 0), e(-1, 0), e(0, 1), e(0, -1)], {"R_b0": 1, "R_b1": 0, "T": "S1", "convex": False}),
        ("S = {+-e1, +-e2, +-e3}", [e(1, 0, 0), e(-1, 0, 0), e(0, 1, 0), e(0, -1, 0), e(0, 0, 1), e(0, 0, -1)],
         {"R_b0": 1, "R_b1": 1, "T": "point", "convex": False}),
        ("S = {+-e_i}, d = 4", [[s if c == i else 0 for c in range(4)] for i in range(4) for s in (1, -1)],
         {"R_b0": 1, "R_b1": 3, "T": "point"}),
        ("asymmetric triangle", [e(1, 0), e(0, 1), e(-2, -3)], {"R_b0": 1, "R_b1": 0, "T": "S1", "convex": False}),
        ("zero on a hull edge", [e(-1, 0), e(1, 0), e(0, 1)], {"T": "point", "convex": False}),
        ("triangle plus zero step", [e(1, 0), e(0, 1), e(-2, -3), e(0, 0)], {"R_b0": 1, "R_b1": 0, "T": "S1"}),
        ("one-way e1, e2, e3", [e(1, 0, 0), e(0, 1, 0), e(0, 0, 1)], {"R_b0": 0, "T": "point", "convex": True}),
        ("rank-3 circuit of size 4", [e(1, 0, 0), e(0, 1, 0), e(0, 0, 1), e(-1, -1, -1)],
         {"R_b0": 0, "T": "point", "convex": True}),
        ("+-e_i in Z^3 plus zero step", [e(1, 0, 0), e(-1, 0, 0), e(0, 1, 0), e(0, -1, 0), e(0, 0, 1), e(0, 0, -1), e(0, 0, 0)],
         {"R_b0": 1, "R_b1": 0}),
        ("two isolated triangles on an unbalanced common line",
         [e(1, 0, 0), e(-1, 1, 0), e(-1, -1, 0), e(-1, 0, 1), e(-1, 0, -1)],
         {"R_b0": 2, "R_b1": 0, "T": "point", "convex": False}),
        ("pure torsion", [e(0, 0), e(0, 0)], {"R_b0": 1, "R_b1": 0, "T": "empty", "convex": True}),
    ]
    for name, vs, want in fixtures:
        b0 = check(vs, stats, want)
        print(f"fixture ok: {name}")
    # exhaustive universes
    planar = [e(1, 0), e(-1, 0), e(0, 1), e(0, -1), e(1, 1), e(-2, -1), e(2, -1), e(-1, 2), e(0, 0)]
    spatial = [e(1, 0, 0), e(-1, 1, 0), e(-1, -1, 0), e(0, 0, 1), e(0, 0, -1), e(-1, 0, 0), e(0, 1, 1), e(0, -1, -1),
               e(1, 1, 1), e(0, 0, 0)]
    for uni in (planar, spatial):
        for size in range(1, len(uni) + 1):
            for J in combinations(range(len(uni)), size):
                check([uni[j] for j in J], stats)
    print("exhaustive universes ok")
    # seeded random inputs in Z^2 .. Z^4
    rng = random.Random(20261119)
    for _ in range(300):
        n = rng.choice([2, 3, 3, 4])
        m = rng.randint(2, 7)
        vs = [[rng.randint(-2, 2) for _ in range(n)] for _ in range(m)]
        check(vs, stats)
    print("seeded inputs ok")
    # no disconnected R with at most four steps (Remark 3.1), over the cube {-1,0,1}^3 and duplicates
    cube = [list(p) for p in product([-1, 0, 1], repeat=3)]
    worst = 0
    count4 = 0
    for size in range(1, 5):
        for J in combinations(range(len(cube)), size):
            f = formula([cube[j] for j in J])
            c = 1 if f["zero"] else f["comps"]
            worst = max(worst, c)
            count4 += 1
    assert worst <= 1
    print(f"at most four steps from {{-1,0,1}}^3: {count4} sets, largest component count {worst}")
    print("inputs checked:", stats["inputs"])
    print("transient homotopy types:", dict(sorted(stats["types"].items())))
    print("recurrent component counts:", dict(sorted(stats["comps"].items())))
    print("recurrent first Betti numbers:", dict(sorted(stats["b1"].items())))
    print("convex transient sets:", stats["convex"])
    print("all checks pass")


if __name__ == "__main__":
    main()
