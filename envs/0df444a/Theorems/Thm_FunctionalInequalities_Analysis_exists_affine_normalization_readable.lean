-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_affine_normalization_readable
-- name    : FunctionalInequalities.Analysis.exists_affine_normalization_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:39.773537+00:00
-- url     : https://prove2.me/theorems/eaae9cde-a1a3-4aa1-8fc7-b6ed5d522bb4
-- title:
--   Affine Normalization of Compact Convex Sets
-- statement:
--   This formalizes the affine normalization statement used in the weak Letwin route.
--
--   Let $E$ be a finite-dimensional real inner-product space. There exists a constant $C>0$, depending only on $E$, such that for every compact convex set $K\subseteq E$ with nonempty interior, there is an affine equivalence $e:E\simeq_A E$ satisfying
--
--   $$
--   \overline B(0,1)\subseteq e(K)\subseteq\overline B(0,C).
--   $$
--
--   The declaration is `exists_affine_normalization_readable`. The result is existential in both $C$ and the affine equivalence and does not provide a uniform constant across different ambient spaces.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_affine_normalization {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
--       [FiniteDimensional ℝ E] :
--       ∃ C : ℝ, 0 < C ∧ ∀ K : Set E, IsCompact K → Convex ℝ K → (interior K).Nonempty →
--         ∃ e : E ≃ᵃ[ℝ] E, closedBall (0 : E) 1 ⊆ e '' K ∧ e '' K ⊆ closedBall (0 : E) C
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Normalization`](https://prove2.me/theorems/c20810ec-8464-4452-b023-bf292cc5b276).
--
--   Supporting theorems: [`abs_simplexCoord_le_one_of_max`](https://prove2.me/theorems/8c17d6d3-6bb3-4149-817e-62c066eb1e35), [`closedBall_subset_stdSimplex_and_box_subset_closedBall`](https://prove2.me/theorems/13e62e66-a24e-43f3-9ca6-0687c2a3f734), [`exists_max_simplexEdgeMatrix_det`](https://prove2.me/theorems/20479a29-7d2f-4cb5-8d1b-e0dbc2e4e013).
--
--   Previous: [`closedBall_subset_stdSimplex_and_box_subset_closedBall`](https://prove2.me/theorems/13e62e66-a24e-43f3-9ca6-0687c2a3f734).
--
--   [Source excerpt, lines 520–523](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Normalization.lean#L520-L523) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Normalization.lean#L515-L736 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Normalization`, declaration `FunctionalInequalities.Analysis.exists_affine_normalization`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Normalization

open Set Metric
set_option maxHeartbeats 4000000

theorem FunctionalInequalities.Analysis.exists_affine_normalization_readable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∃ C : ℝ, 0 < C ∧ ∀ K : Set E, IsCompact K → Convex ℝ K → (interior K).Nonempty →
      ∃ e : E ≃ᵃ[ℝ] E, closedBall (0 : E) 1 ⊆ e '' K ∧ e '' K ⊆ closedBall (0 : E) C := by sorry
