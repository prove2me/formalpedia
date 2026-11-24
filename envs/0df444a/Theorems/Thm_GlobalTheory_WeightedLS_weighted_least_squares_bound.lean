-- Prove2me | Theorems.Thm_GlobalTheory_WeightedLS_weighted_least_squares_bound
-- name    : GlobalTheory.WeightedLS.weighted_least_squares_bound
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:52:43.467287+00:00
-- url     : https://prove2.me/theorems/e5cffad1-737f-4312-bb72-11c44bccc923
-- title:
--   Weighted LS: weighted least squares bound
-- statement:
--   The Weighted LS construction uses the weighted least squares bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeightedLeastSquaresBound.lean#L58-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeightedLeastSquaresBound.lean#L58-L102

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CBinet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLeastSquaresBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder Matrix
open GlobalTheory GlobalTheory.WeightedLS
open Matrix
variable {M g : ℕ}

theorem GlobalTheory.WeightedLS.weighted_least_squares_bound : ∀ (M g : ℕ) (L : Matrix (Fin M) (Fin g) ℝ), L.rank = g →
    ∃ K : ℝ, ∀ (D : Fin M → ℝ) (b : Fin M → ℝ), (∀ k, 0 < D k) →
      ‖((L.transpose * Matrix.diagonal D * L)⁻¹ * L.transpose * Matrix.diagonal D).mulVec b‖ ≤
        K * ‖b‖ := by sorry
