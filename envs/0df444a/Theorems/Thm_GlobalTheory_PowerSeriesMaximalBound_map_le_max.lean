-- Prove2me | Theorems.Thm_GlobalTheory_PowerSeriesMaximalBound_map_le_max
-- name    : GlobalTheory.PowerSeriesMaximalBound.map_le_max
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:54:42.523036+00:00
-- url     : https://prove2.me/theorems/3f5543c2-10b7-4768-b525-1d1390820fe7
-- title:
--   Power Series Maximal Bound: map le max
-- statement:
--   The Power Series Maximal Bound construction uses the map le max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MonomialOneMem.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MonomialOneMem.lean#L17-L22

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

theorem GlobalTheory.PowerSeriesMaximalBound.map_le_max :
    Ideal.map (C : O →+* MvPowerSeries (Fin a) O) (IsLocalRing.maximalIdeal O)
      ≤ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) := by sorry
