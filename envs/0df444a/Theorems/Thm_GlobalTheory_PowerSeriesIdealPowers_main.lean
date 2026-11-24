-- Prove2me | Theorems.Thm_GlobalTheory_PowerSeriesIdealPowers_main
-- name    : GlobalTheory.PowerSeriesIdealPowers.main
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:54:44.847379+00:00
-- url     : https://prove2.me/theorems/7069564b-30a7-4c08-be10-9add0871b680
-- title:
--   Power Series Ideal Powers: main
-- statement:
--   The Power Series Ideal Powers construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MemPowOfCoeffMem.lean#L114-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MemPowOfCoeffMem.lean#L114-L139

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MemPowOfCoeffMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerSeriesIdealPowers
open MvPowerSeries IsLocalRing
variable {O : Type} [CommRing O] [IsLocalRing O]

theorem GlobalTheory.PowerSeriesIdealPowers.main : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O]
    [IsPrecomplete (IsLocalRing.maximalIdeal O) O] (a : ℕ),
    IsPrecomplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O)) (MvPowerSeries (Fin a) O) := by sorry
