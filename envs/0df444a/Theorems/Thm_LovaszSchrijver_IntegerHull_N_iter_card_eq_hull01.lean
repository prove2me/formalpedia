-- Prove2me | Theorems.Thm_LovaszSchrijver_IntegerHull_N_iter_card_eq_hull01
-- name    : LovaszSchrijver.IntegerHull.N_iter_card_eq_hull01
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:43:52.62077+00:00
-- url     : https://prove2.me/theorems/32d53bf7-3423-4ea2-baa3-304ea1f462d9
-- title:
--   Theorem 1.4 — n rounds of N give the cone spanned by the 0–1 vectors of K
-- statement:
--   Let $K \subseteq Q$ be a closed convex cone in $\mathbb R^{n+1}$, where $Q$ is the cone spanned by the 0–1 vectors with $x_0 = 1$. Let $N(K) = N(K, Q)$ be the Lovász–Schrijver cut operator, $N^0(K) = K$ and $N^t(K) = N(N^{t-1}(K))$. Then
--   $$N^n(K) = K^\circ,$$
--   where $K^\circ$ is the cone spanned by all 0–1 vectors in $K$.
--
--   Dehomogenized at $x_0 = 1$, this says that $n$ rounds of the operator $N$, applied to any relaxation of a 0–1 program in $n$ variables, yield exactly the convex hull of its 0–1 solutions: the $N$ hierarchy is exact at level $n$.
--
--   **Formalization Note** Coordinates of $\mathbb R^{n+1}$ are indexed by `Option ι` with `none` the 0th coordinate, and $n$ is the cardinality of the finite type `ι` (which may be $0$). The paper tacitly takes $K$ closed (polyhedral in all its applications); the rewriting (iii′) on p. 169 needs it, and without it the statement is false: for the cone $\{x : 0 < x_1 < x_0\} \cup \{0\}$ in $\mathbb R^2$ one has $K^\circ = \{0\}$ while $N(K) = Q$.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 171, Theorem 1.4

import Mathlib
import Definitions.Def_LovaszSchrijver_IntegerHull_Basic
import Definitions.Def_LovaszSchrijver_IntegerHull_MatrixCone
open Matrix Pointwise

namespace LovaszSchrijver.IntegerHull

theorem N_iter_card_eq_hull01 {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : Set (Option ι → ℝ)) (hK : IsConvexCone K) (hKc : IsClosed K) (hKQ : K ⊆ Q) :
    Niter (Fintype.card ι) K = hull01 K := by sorry

end LovaszSchrijver.IntegerHull
