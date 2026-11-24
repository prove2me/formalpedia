-- Prove2me | Theorems.Thm_GlobalTheory_PowerSeriesMaximalBound_X_mem_max
-- name    : GlobalTheory.PowerSeriesMaximalBound.X_mem_max
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:54:35.69416+00:00
-- url     : https://prove2.me/theorems/ece925c0-03b5-438c-a04b-8b873bc9bf27
-- title:
--   Power Series Maximal Bound: X mem max
-- statement:
--   The Power Series Maximal Bound construction uses the X mem max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MonomialOneMem.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MonomialOneMem.lean#L12-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MonomialOneMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerSeriesMaximalBound
open MvPowerSeries
variable {O : Type} [CommRing O] [IsLocalRing O] {a : ℕ}

theorem GlobalTheory.PowerSeriesMaximalBound.X_mem_max (i : Fin a) :
    (X i : MvPowerSeries (Fin a) O) ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) := by sorry
