-- Prove2me | Theorems.Thm_GlobalTheory_FiltrationMultiplicative_part_mem
-- name    : GlobalTheory.FiltrationMultiplicative.part_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:23:56.088586+00:00
-- url     : https://prove2.me/theorems/6c4d6a22-d627-4949-aa70-92e18b9a468c
-- title:
--   Filtration Multiplicative: part mem
-- statement:
--   The Filtration Multiplicative construction uses the part mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiltLePow.lean#L132-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiltLePow.lean#L132-L141

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

theorem GlobalTheory.FiltrationMultiplicative.part_mem {a N : ℕ} {f : MvPowerSeries (Fin a) O} (hf : f ∈ Filt O (Fin a) (N + 1))
    (i : Fin a) : part f i ∈ Filt O (Fin a) N := by sorry
