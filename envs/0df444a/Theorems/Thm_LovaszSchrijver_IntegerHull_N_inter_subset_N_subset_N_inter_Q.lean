-- Prove2me | Theorems.Thm_LovaszSchrijver_IntegerHull_N_inter_subset_N_subset_N_inter_Q
-- name    : LovaszSchrijver.IntegerHull.N_inter_subset_N_subset_N_inter_Q
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:43:20.673678+00:00
-- url     : https://prove2.me/theorems/75e5009f-d06a-4ff4-a209-99da2e343826
-- title:
--   Remark after Lemma 1.1 — N(K₁ ∩ K₂, K₁ ∩ K₂) ⊆ N(K₁, K₂) ⊆ N(K₁ ∩ K₂, Q)
-- statement:
--   Let $K_1, K_2 \subseteq Q$ be closed convex cones in $\mathbb R^{n+1}$. Then
--   $$N(K_1 \cap K_2, K_1 \cap K_2) \subseteq N(K_1, K_2) \subseteq N(K_1 \cap K_2, Q).$$
--
--   The paper introduces it with "It is easy to see that"; it explains why it suffices to study the two special choices $K_1 = K_2 = K$ and $K_1 = K$, $K_2 = Q$, and the operator $N(K) = N(K, Q)$ that is iterated in Theorem 1.4.
--
--   **Formalization Note** The right-hand inclusion uses the rewriting (iii′), which needs $K_i^{**} = K_i$; the paper tacitly takes the cones closed (polyhedral in all its applications), and both cones are assumed closed.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 170, Section 1.a (display after Lemma 1.1)

import Mathlib
import Definitions.Def_LovaszSchrijver_IntegerHull_Basic
import Definitions.Def_LovaszSchrijver_IntegerHull_MatrixCone
open Matrix Pointwise

namespace LovaszSchrijver.IntegerHull

theorem N_inter_subset_N_subset_N_inter_Q {ι : Type} [Fintype ι] [DecidableEq ι]
    (K₁ K₂ : Set (Option ι → ℝ)) (hK₁ : IsConvexCone K₁) (hK₂ : IsConvexCone K₂)
    (hK₁c : IsClosed K₁) (hK₂c : IsClosed K₂) (hK₁Q : K₁ ⊆ Q) (hK₂Q : K₂ ⊆ Q) :
    N (K₁ ∩ K₂) (K₁ ∩ K₂) ⊆ N K₁ K₂ ∧ N K₁ K₂ ⊆ N (K₁ ∩ K₂) Q := by sorry

end LovaszSchrijver.IntegerHull
