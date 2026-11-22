# Topology of the recurrent and transient parameter sets of random walks on abelian groups

Yitzchak Shmalo

DOI: [10.5281/zenodo.24449616](https://doi.org/10.5281/zenodo.24449616) (all versions); version 1.0: [10.5281/zenodo.24449617](https://doi.org/10.5281/zenodo.24449617)

Fix a finitely generated abelian group and a finite set S of steps, and let R be the set of probability vectors on S
whose homogeneous random walk is recurrent. Li, Mossel and Weiss characterized R and asked when R is simply connected
and when its complement is path connected, simply connected or convex. When no step projects to zero in the free part
of the group, R is homotopy equivalent to a finite bipartite graph of lines and planes spanned by projections of
steps, so it is simply connected only when it is contractible. The complement is empty, contractible, homotopy
equivalent to two points, or homotopy equivalent to a circle, according to the rank of the projections and whether the
origin is in the relative interior of their convex hull. It is convex exactly when no two or three nonzero projections
of steps are positively dependent.

- `main.tex`, `main.pdf`: the paper.
- `check_lmw.py`: exact checks in rational arithmetic (standard library only). It compares the nerve of the cover of
  R by zero-drift polytopes with the component count and rank formula of Theorem 1.2, checks the certificates in the
  proof of Theorem 1.5 and the convexity criterion of Theorem 1.7 on seeded and random step sets, and confirms that
  no step set with at most four steps from {-1,0,1}^3 has a disconnected R. Run with `python check_lmw.py`.

See `CREDITS.md` for the work this paper builds on.
