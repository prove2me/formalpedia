-- Prove2me | Theorems.Thm_GlobalTheory_PowerSeriesCoeffSum_eq_sum
-- name    : GlobalTheory.PowerSeriesCoeffSum.eq_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:52:26.899041+00:00
-- url     : https://prove2.me/theorems/f393ee05-e2cd-4ede-9b6d-2b8ff17bd355
-- title:
--   Power Series Coeff Sum: eq sum
-- statement:
--   The Power Series Coeff Sum construction uses the eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/CoeffXMulPart.lean#L34-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/CoeffXMulPart.lean#L34-L58

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

theorem GlobalTheory.PowerSeriesCoeffSum.eq_sum (f : MvPowerSeries (Fin a) O) (h0 : coeff 0 f = 0) :
    f = ∑ i, X i * part f i := by sorry
