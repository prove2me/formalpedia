-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_sum_le_sqrt_card_mul_sqrt_sum_sq
-- name    : GlobalTheory.MvPoly.sum_le_sqrt_card_mul_sqrt_sum_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:06:10.120825+00:00
-- url     : https://prove2.me/theorems/0c24603e-6688-437b-8914-fa4260b03642
-- title:
--   Mv Poly: sum le sqrt card mul sqrt sum sq
-- statement:
--   The Mv Poly construction uses the sum le sqrt card mul sqrt sum sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L152-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L152-L155

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open GlobalTheory GlobalTheory.MvPoly
variable {σ τ K L : Type*}
variable [NormedCommRing K]

theorem GlobalTheory.MvPoly.sum_le_sqrt_card_mul_sqrt_sum_sq {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ s, f i ≤ √(#s) * √(∑ i ∈ s, f i ^ 2) := by sorry
