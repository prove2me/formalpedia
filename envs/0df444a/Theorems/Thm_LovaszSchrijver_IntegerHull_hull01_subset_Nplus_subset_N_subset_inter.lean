-- Prove2me | Theorems.Thm_LovaszSchrijver_IntegerHull_hull01_subset_Nplus_subset_N_subset_inter
-- name    : LovaszSchrijver.IntegerHull.hull01_subset_Nplus_subset_N_subset_inter
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:41:45.663644+00:00
-- url     : https://prove2.me/theorems/a64d5ba0-0cd9-464c-a99b-a6136d414886
-- title:
--   Lemma 1.1 — (K₁ ∩ K₂)° ⊆ N₊(K₁, K₂) ⊆ N(K₁, K₂) ⊆ K₁ ∩ K₂
-- statement:
--   Let $K_1, K_2 \subseteq Q$ be closed convex cones in $\mathbb R^{n+1}$. Then
--   $$(K_1 \cap K_2)^\circ \subseteq N_+(K_1, K_2) \subseteq N(K_1, K_2) \subseteq K_1 \cap K_2 .$$
--   Here $(K_1 \cap K_2)^\circ$ is the cone spanned by the 0–1 vectors in $K_1 \cap K_2$.
--
--   The lemma says that the operators $N$ and $N_+$ are relaxation-tightening cuts: they never lose a 0–1 point and never add a point outside the cones they start from.
--
--   **Formalization Note** The three inclusions are stated as one conjunction. The last inclusion uses the rewriting (iii′), which needs $K_i^{**} = K_i$; the paper tacitly takes the cones closed (polyhedral in all its applications), so both cones are assumed closed. For a non-closed cone the last inclusion can fail.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 170, Lemma 1.1

import Mathlib
import Definitions.Def_LovaszSchrijver_IntegerHull_Basic
import Definitions.Def_LovaszSchrijver_IntegerHull_MatrixCone
open Matrix Pointwise

namespace LovaszSchrijver.IntegerHull

theorem hull01_subset_Nplus_subset_N_subset_inter {ι : Type} [Fintype ι] [DecidableEq ι]
    (K₁ K₂ : Set (Option ι → ℝ)) (hK₁ : IsConvexCone K₁) (hK₂ : IsConvexCone K₂)
    (hK₁c : IsClosed K₁) (hK₂c : IsClosed K₂) (hK₁Q : K₁ ⊆ Q) (hK₂Q : K₂ ⊆ Q) :
    hull01 (K₁ ∩ K₂) ⊆ Nplus K₁ K₂ ∧ Nplus K₁ K₂ ⊆ N K₁ K₂ ∧ N K₁ K₂ ⊆ K₁ ∩ K₂ := by sorry

end LovaszSchrijver.IntegerHull
