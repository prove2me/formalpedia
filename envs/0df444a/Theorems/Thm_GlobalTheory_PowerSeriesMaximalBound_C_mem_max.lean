-- Prove2me | Theorems.Thm_GlobalTheory_PowerSeriesMaximalBound_C_mem_max
-- name    : GlobalTheory.PowerSeriesMaximalBound.C_mem_max
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:54:28.932171+00:00
-- url     : https://prove2.me/theorems/57348c24-9fec-4fda-8e37-09518108161a
-- title:
--   Power Series Maximal Bound: C mem max
-- statement:
--   The Power Series Maximal Bound construction uses the C mem max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MonomialOneMem.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MonomialOneMem.lean#L7-L10

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

theorem GlobalTheory.PowerSeriesMaximalBound.C_mem_max {r : O} (hr : r ∈ IsLocalRing.maximalIdeal O) :
    (C r : MvPowerSeries (Fin a) O) ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) := by sorry
