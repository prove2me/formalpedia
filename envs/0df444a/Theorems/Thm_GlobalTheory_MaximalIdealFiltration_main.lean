-- Prove2me | Theorems.Thm_GlobalTheory_MaximalIdealFiltration_main
-- name    : GlobalTheory.MaximalIdealFiltration.main
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:20:43.920689+00:00
-- url     : https://prove2.me/theorems/da0fed3a-62db-48e0-81e9-2e40034667c5
-- title:
--   Maximal Ideal Filtration: main
-- statement:
--   The Maximal Ideal Filtration construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MaximalIdealLeFiltOne.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MaximalIdealLeFiltOne.lean#L73-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MaximalIdealLeFiltOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MaximalIdealFiltration
open MvPowerSeries
variable {O : Type} [CommRing O] [IsLocalRing O] {a : ℕ}

theorem GlobalTheory.MaximalIdealFiltration.main : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O] {a : ℕ} (N : ℕ), ∀ f ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ N, ∀ (m : Fin a →₀ ℕ), (MvPowerSeries.coeff m : MvPowerSeries (Fin a) O → O) f ∈ IsLocalRing.maximalIdeal O ^ (N - (Finsupp.degree : (Fin a →₀ ℕ) → ℕ) m) := by sorry
