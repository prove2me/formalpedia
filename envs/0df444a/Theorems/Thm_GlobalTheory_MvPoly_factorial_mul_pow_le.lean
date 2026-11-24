-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_factorial_mul_pow_le
-- name    : GlobalTheory.MvPoly.factorial_mul_pow_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:28:55.765214+00:00
-- url     : https://prove2.me/theorems/9dae2cfa-54fc-4a8a-9b61-4ef7018accc9
-- title:
--   Mv Poly: factorial mul pow le
-- statement:
--   The Mv Poly construction uses the factorial mul pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L197-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L197-L200

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

theorem GlobalTheory.MvPoly.factorial_mul_pow_le (i : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (i.factorial : ℝ) * R ^ i ≤ (i * R) ^ i := by sorry
