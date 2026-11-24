-- Prove2me | Theorems.Thm_GlobalTheory_FiltrationMultiplicative_main
-- name    : GlobalTheory.FiltrationMultiplicative.main
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:23:58.696285+00:00
-- url     : https://prove2.me/theorems/bd2cf523-2382-4fb2-a0c8-da80da43b784
-- title:
--   Filtration Multiplicative: main
-- statement:
--   The Filtration Multiplicative construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiltLePow.lean#L170-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiltLePow.lean#L170-L176

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

theorem GlobalTheory.FiltrationMultiplicative.main : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O] {a : ℕ} (N : ℕ)
    (f : MvPowerSeries (Fin a) O),
    f ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ N ↔
      ∀ (m : Fin a →₀ ℕ), (MvPowerSeries.coeff m : MvPowerSeries (Fin a) O → O) f ∈
        IsLocalRing.maximalIdeal O ^ (N - (Finsupp.degree : (Fin a →₀ ℕ) → ℕ) m) := by sorry
