-- Prove2me | Theorems.Thm_GlobalTheory_FiltrationMultiplicative_isFirst_unique
-- name    : GlobalTheory.FiltrationMultiplicative.isFirst_unique
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:24:57.186594+00:00
-- url     : https://prove2.me/theorems/793cb214-5524-4edf-ab1c-57e184f73472
-- title:
--   Filtration Multiplicative: is First unique
-- statement:
--   The Filtration Multiplicative construction uses the is First unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiltLePow.lean#L77-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiltLePow.lean#L77-L82

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

theorem GlobalTheory.FiltrationMultiplicative.isFirst_unique {a : ℕ} {m : Fin a →₀ ℕ} {i j : Fin a} (hi : IsFirst m i)
    (hj : IsFirst m j) : i = j := by sorry
