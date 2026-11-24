-- Prove2me | Theorems.Thm_GlobalTheory_exists_short_basis_of_ratSpan
-- name    : GlobalTheory.exists_short_basis_of_ratSpan
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:42:36.786474+00:00
-- url     : https://prove2.me/theorems/41127242-26a6-4856-a214-12a6c4a4fe94
-- title:
--   Global Theory: exists short basis of rat Span
-- statement:
--   The Global Theory construction uses the exists short basis of rat Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsReducedBasisIntegralPartOfLinearIndependen.lean#L11-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsReducedBasisIntegralPartOfLinearIndependen.lean#L11-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsShortBasisAdaptedOfSubsetSpan
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsReducedBasisIntegralPartOfLinearIndependen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule MvPolynomial NumberField
open GlobalTheory

theorem GlobalTheory.exists_short_basis_of_ratSpan {V E ι : Type*} [AddCommGroup V] [Module ℚ V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (H : Submodule ℤ V) (φ : V →+ E) {ε : ℝ} (hε : 0 < ε)
    (hφ : ∀ x ∈ H, x ≠ 0 → ε ≤ ‖φ x‖) (v : ι → V) (hvH : ∀ j, v j ∈ H)
    (hsp : (H : Set V) ⊆ span ℚ (Set.range v)) {r : ℝ} (hr : ∀ j, ‖φ (v j)‖ ≤ r) {R : ℕ}
    (hR : R = finrank ℚ (span ℚ (Set.range v))) :
    ∃ b : Basis (Fin R) ℤ H, ∀ i, ‖φ (b i)‖ ^ 2 ≤ ((R + 3 : ℝ) / 4) * r ^ 2 := by sorry
