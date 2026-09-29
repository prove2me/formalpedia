-- Prove2me | Theorems.Thm_LovaszSchrijver_OddHole_N_subset_H_add_G
-- name    : LovaszSchrijver.OddHole.N_subset_H_add_G
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:47:08.220483+00:00
-- url     : https://prove2.me/theorems/634332ae-fe7d-4f9c-9ed3-98291da383d0
-- title:
--   Lemma 1.3 — N(K) ⊆ (K ∩ Hᵢ) + (K ∩ Gᵢ)
-- statement:
--   Let $K \subseteq Q$ be a closed convex cone in $\mathbb{R}^{n+1}$, where $Q$ is the cone spanned by the 0–1 vectors with $x_0 = 1$, and let $1 \le i \le n$. With $H_i = \{x : x_i = 0\}$ and $G_i = \{x : x_i = x_0\}$,
--   $$N(K) \subseteq (K \cap H_i) + (K \cap G_i),$$
--   where $N(K) = \{Y e_0 : Y \in M(K, Q)\}$ and the sum is the Minkowski sum of sets.
--
--   The lemma is the paper's geometric description of one round of the $N$ operator: every point of $N(K)$ splits into a point of $K$ on the face $x_i = 0$ of $Q$ and a point of $K$ on the opposite face $x_i = x_0$. It is the ingredient behind Lemma 2.2.
--
--   **Formalization Note** The paper states the lemma for every convex cone $K \subseteq Q$; closedness of $K$ is added. Condition (iii) sees $K$ only through its polar, so $N(K) = N(\overline K)$, and for a non-closed cone the inclusion can fail (the cone $\{x : 0 < x_1 < x_0\} \cup \{0\}$ in $\mathbb{R}^2$ has $N(K) = Q$). The paper tacitly takes $K$ closed (polyhedral in all its applications); the rewriting (iii′) on p. 169 needs it.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 171, Lemma 1.3

import Mathlib
import Definitions.Def_LovaszSchrijver_OddHole_MatrixCone
import Definitions.Def_LovaszSchrijver_OddHole_FacetHyperplanes

open Pointwise

namespace LovaszSchrijver.OddHole

/-- Lemma 1.3 (p. 171): for every (closed) convex cone `K ⊆ Q` and every `1 ≤ i ≤ n`,
`N(K) ⊆ (K ∩ Hᵢ) + (K ∩ Gᵢ)`. -/
theorem N_subset_H_add_G {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : Set (Option ι → ℝ)) (hK : IsConvexCone K) (hKc : IsClosed K) (hKQ : K ⊆ Q ι)
    (i : ι) :
    N K ⊆ (K ∩ Hplane i) + (K ∩ Gplane i) := by sorry

end LovaszSchrijver.OddHole
