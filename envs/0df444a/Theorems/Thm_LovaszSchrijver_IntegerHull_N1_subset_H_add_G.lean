-- Prove2me | Theorems.Thm_LovaszSchrijver_IntegerHull_N1_subset_H_add_G
-- name    : LovaszSchrijver.IntegerHull.N1_subset_H_add_G
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:42:07.639456+00:00
-- url     : https://prove2.me/theorems/99ed522f-fbd3-4ed5-b366-bb2b72511709
-- title:
--   Lemma 1.3 — N(K) ⊆ (K ∩ Hᵢ) + (K ∩ Gᵢ)
-- statement:
--   Let $K \subseteq Q$ be a closed convex cone in $\mathbb R^{n+1}$, and let $1 \le i \le n$. With $H_i = \{x : x_i = 0\}$ and $G_i = \{x : x_i = x_0\}$,
--   $$N(K) \subseteq (K \cap H_i) + (K \cap G_i),$$
--   where $+$ is the Minkowski sum $\{y + z : y \in K\cap H_i,\ z \in K \cap G_i\}$ and $N(K) = N(K, Q)$.
--
--   This is the geometric property of $N(K)$: every point of $N(K)$ splits into a point of $K$ on the facet $x_i = 0$ of $Q$ and a point of $K$ on the opposite facet $x_i = x_0$. It is the base case ($t = 1$) of the induction proving Theorem 1.4.
--
--   **Formalization Note** The paper's proof goes through (iii″), which needs $K$ closed; the paper tacitly takes $K$ closed (polyhedral in all its applications), and the hypothesis is added. Without it the statement fails (for the cone $\{x : 0 < x_1 < x_0\} \cup \{0\}$ in $\mathbb R^2$, $N(K) = Q$ while the right-hand side is $\{0\}$).
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 171, Lemma 1.3

import Mathlib
import Definitions.Def_LovaszSchrijver_IntegerHull_Basic
import Definitions.Def_LovaszSchrijver_IntegerHull_MatrixCone
open Matrix Pointwise

namespace LovaszSchrijver.IntegerHull

theorem N1_subset_H_add_G {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : Set (Option ι → ℝ)) (hK : IsConvexCone K) (hKc : IsClosed K) (hKQ : K ⊆ Q) (i : ι) :
    N1 K ⊆ (K ∩ H i) + (K ∩ G i) := by sorry

end LovaszSchrijver.IntegerHull
