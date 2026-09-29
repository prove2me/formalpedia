-- Prove2me | Theorems.Thm_KServer_manhattan_parallel_bundle
-- name    : KServer.manhattan_parallel_bundle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T15:16:26.137185+00:00
-- url     : https://prove2.me/theorems/c72ad2e8-c000-4bb6-a18f-9c0ae6ee4b3d
-- title:
--   Parallel bundle decomposition in the sup metric
-- statement:
--   Bein, Chrobak and Larmore's proof that the Work Function Algorithm is $3$-competitive for three servers in the Manhattan plane rests on one purely geometric property of that space, isolated as their Lemma 5. This is that lemma.
--
--   ## Linear tuples and parallel bundles
--
--   In a metric space, a tuple $(x_1,\dots,x_m)$ is **linear** if $x_ix_j + x_jx_\ell = x_ix_\ell$ whenever $i \le j \le \ell$ — the points lie in this order along a geodesic. Two ordered pairs $(a,b)$ and $(c,d)$ are **parallel** if there are points $x,y$ making both $(x,a,b,y)$ and $(x,c,d,y)$ linear; a family of pairs is a **parallel bundle** if a single pair of *poles* $x,y$ works for all of them simultaneously. Unordered pairs count as parallel if they can be oriented to be.
--
--   ## The statement
--
--   Let $\mathbb{R}^d_\infty$ be $\mathbb{R}^d$ under the sup metric $xy = \max_i |x_i - y_i|$; for $d = 2$ this is isometric, by a rotation through $45°$ and a scaling, to the Manhattan metric $|x_1-y_1| + |x_2-y_2|$ on the plane. Then **every set of pairs of points drawn from a bounded set is a union of at most $d$ parallel bundles.** For $d = 2$ — the Manhattan plane — every family of pairs splits into at most *two* bundles, and it is this dichotomy that drives the case analysis of the competitiveness proof.
--
--   Formally: given a bound $N$ on all coordinates of all points of $S$, there are $d$ pairs of poles $x_i, y_i$ such that every $a, b \in S$ lie, in one of their two orders, on a geodesic from $x_i$ to $y_i$ for some coordinate $i$. The four displayed equations are exactly linearity of the $4$-tuple.
--
--   ## The construction
--
--   The proof is short and completely explicit. Assign to a pair $\{a,b\}$ any coordinate $i$ realising its distance, $ab = |a_i - b_i|$ — one exists because the sup over the finitely many coordinates is attained. For that coordinate take the poles
--   $$x_i = 2N \cdot e_i, \qquad y_i = -2N \cdot e_i,$$
--   that is, $2N$ and $-2N$ in coordinate $i$ and $0$ elsewhere. For any point $c$ of $S$,
--   $$x_ic = \max\bigl(|2N - c_i|,\ \max_{j \ne i} |c_j|\bigr) = 2N - c_i,$$
--   because $|c_i| \le N$ forces $2N - c_i \ge N$, which already dominates every other coordinate; symmetrically $y_ic = 2N + c_i$, and $x_iy_i = 4N$. So *every* point of $S$ lies on a geodesic from $x_i$ to $y_i$, its position along that geodesic being read off its $i$-th coordinate. Ordering the pair so that $b_i \le a_i$, the four linearity equations become
--   $$(2N - a_i) + (a_i - b_i) = 2N - b_i, \quad (a_i - b_i) + (2N + b_i) = 2N + a_i,$$
--   $$(2N - a_i) + (2N + a_i) = 4N, \quad (2N - b_i) + (2N + b_i) = 4N,$$
--   all immediate — and the middle step uses precisely the hypothesis $ab = |a_i - b_i|$, which is what confines the pair to the bundle in direction $i$.
--
--   ## Remarks
--
--   The bound $N$ enters only to guarantee that the poles are far enough out that the $i$-th coordinate dominates; any $N$ bounding the coordinates of $S$ works, so the statement applies to every bounded set, in particular to every finite one, which is the case used in the application. The hypothesis $d > 0$ is needed only so that a coordinate realising the distance exists.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, EXTENDED ABSTRACT, Algorithms - ESA'99, 7th Annual European Symposium, LNCS 1643, Springer (1999) 301-312, Section 4, Lemma 5: 'Let B be a finite set of pairs of points in R^d_infinity. Then B is a union of at most d parallel bundles', together with the definitions of linear m-tuple and parallel bundle given in the same section. NOTE ON THE SOURCE: this statement belongs to the ESA'99 extended abstract only. The journal version (Theoretical Computer Science 289(1) (2002) 335-354) restructures the Manhattan argument and does not use parallel bundles at all - the word does not occur in it - proving the two required inequalities directly from the triangle inequality, the Lipschitz property and quasiconvexity. In particular 'Lemma 5' of the journal version is a DIFFERENT statement (Lambda_{omega,r} <= Psi_{omega,r} in the Manhattan plane) and must not be confused with this one.

import Mathlib

namespace KServer

theorem manhattan_parallel_bundle {d : ℕ} (hd : 0 < d) (N : ℝ) (hN : 0 ≤ N)
    (S : Set (Fin d → ℝ)) (hS : ∀ a ∈ S, ∀ j, |a j| ≤ N) :
    ∃ x y : Fin d → (Fin d → ℝ), ∀ a ∈ S, ∀ b ∈ S, ∃ i : Fin d,
      (dist (x i) a + dist a b = dist (x i) b ∧
        dist a b + dist b (y i) = dist a (y i) ∧
        dist (x i) a + dist a (y i) = dist (x i) (y i) ∧
        dist (x i) b + dist b (y i) = dist (x i) (y i)) ∨
      (dist (x i) b + dist b a = dist (x i) a ∧
        dist b a + dist a (y i) = dist b (y i) ∧
        dist (x i) b + dist b (y i) = dist (x i) (y i) ∧
        dist (x i) a + dist a (y i) = dist (x i) (y i)) := by sorry

end KServer
