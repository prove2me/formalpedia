-- Prove2me | Theorems.Thm_GlobalTheory_FiltrationMultiplicative_max_le_filt_one
-- name    : GlobalTheory.FiltrationMultiplicative.max_le_filt_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:24:07.788915+00:00
-- url     : https://prove2.me/theorems/c880f6b4-fffa-4842-b6df-9fda9bad7556
-- title:
--   Filtration Multiplicative: max le filt one
-- statement:
--   The Filtration Multiplicative construction uses the max le filt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiltLePow.lean#L55-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiltLePow.lean#L55-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiltLePow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open GlobalTheory GlobalTheory.FiltrationMultiplicative
variable {O : Type} [CommRing O] [IsLocalRing O]

theorem GlobalTheory.FiltrationMultiplicative.max_le_filt_one {σ : Type} :
    IsLocalRing.maximalIdeal (MvPowerSeries σ O) ≤ FiltIdeal O σ 1 := by sorry
