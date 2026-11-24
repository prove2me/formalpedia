-- Prove2me | Theorems.Thm_GlobalTheory_PowerSeriesIdealPowers_C_mem_pow
-- name    : GlobalTheory.PowerSeriesIdealPowers.C_mem_pow
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:54:28.026207+00:00
-- url     : https://prove2.me/theorems/fab8acd0-f2df-4c44-aa04-9d9922f6be1e
-- title:
--   Power Series Ideal Powers: C mem pow
-- statement:
--   The Power Series Ideal Powers construction uses the C mem pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MemPowOfCoeffMem.lean#L50-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MemPowOfCoeffMem.lean#L50-L58

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

theorem GlobalTheory.PowerSeriesIdealPowers.C_mem_pow {σ : Type} (n : ℕ) (c : O) (hc : c ∈ (maximalIdeal O) ^ n) :
    C c ∈ (maximalIdeal (MvPowerSeries σ O)) ^ n := by sorry
