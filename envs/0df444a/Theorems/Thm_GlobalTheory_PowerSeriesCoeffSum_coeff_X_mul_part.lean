-- Prove2me | Theorems.Thm_GlobalTheory_PowerSeriesCoeffSum_coeff_X_mul_part
-- name    : GlobalTheory.PowerSeriesCoeffSum.coeff_X_mul_part
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:52:24.338865+00:00
-- url     : https://prove2.me/theorems/ba800342-6128-44e0-ac55-0fec2e44968e
-- title:
--   Power Series Coeff Sum: coeff X mul part
-- statement:
--   The Power Series Coeff Sum construction uses the coeff X mul part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/CoeffXMulPart.lean#L15-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/CoeffXMulPart.lean#L15-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CoeffXMulPart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerSeriesCoeffSum
open MvPowerSeries Finsupp
variable {O : Type} [CommRing O] {a : ℕ}

theorem GlobalTheory.PowerSeriesCoeffSum.coeff_X_mul_part (f : MvPowerSeries (Fin a) O) (i : Fin a) (m : Fin a →₀ ℕ) :
    coeff m (X i * part f i) = if (1 ≤ m i ∧ ∀ j < i, m j = 0) then coeff m f else 0 := by sorry
