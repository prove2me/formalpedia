-- Prove2me | Theorems.Thm_GlobalTheory_PowerSeriesCoeffSum_coeff_part
-- name    : GlobalTheory.PowerSeriesCoeffSum.coeff_part
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:13.547839+00:00
-- url     : https://prove2.me/theorems/de349e34-055a-4800-b040-f07b7e38b621
-- title:
--   Power Series Coeff Sum: coeff part
-- statement:
--   The Power Series Coeff Sum construction uses the coeff part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/CoeffXMulPart.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/CoeffXMulPart.lean#L12-L13

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

theorem GlobalTheory.PowerSeriesCoeffSum.coeff_part (f : MvPowerSeries (Fin a) O) (i : Fin a) (e : Fin a →₀ ℕ) :
    coeff e (part f i) = if (∀ j < i, e j = 0) then coeff (e + single i 1) f else 0 := by sorry
