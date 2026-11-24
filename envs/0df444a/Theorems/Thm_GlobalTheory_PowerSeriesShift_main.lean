-- Prove2me | Theorems.Thm_GlobalTheory_PowerSeriesShift_main
-- name    : GlobalTheory.PowerSeriesShift.main
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:54:01.440449+00:00
-- url     : https://prove2.me/theorems/0eb0271c-84cc-4a46-8f60-c93afcf2f990
-- title:
--   Power Series Shift: main
-- statement:
--   The Power Series Shift construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/EqXMulShiftAdd.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/EqXMulShiftAdd.lean#L29-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqXMulShiftAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerSeriesShift

theorem GlobalTheory.PowerSeriesShift.main : (let d1 : {σ O : Type} → [CommRing O] → σ → MvPowerSeries σ O → MvPowerSeries σ O := @(fun {σ O : Type} [CommRing O] (i : σ) (f : MvPowerSeries σ O) (m : σ →₀ ℕ) ↦ (MvPowerSeries.coeff ((fun₀ | i => (1 : ℕ)) + m) : MvPowerSeries σ O → O) f); let d2 : {σ O : Type} → [CommRing O] → σ → MvPowerSeries σ O → MvPowerSeries σ O := @(fun {σ O : Type} [CommRing O] (i : σ) (f : MvPowerSeries σ O) (m : σ →₀ ℕ) ↦ if (m : σ → ℕ) i = (0 : ℕ) then (MvPowerSeries.coeff m : MvPowerSeries σ O → O) f else (0 : O)); ∀ {σ O : Type} [inst : CommRing O] (i : σ) (f : MvPowerSeries σ O), f = MvPowerSeries.X i * d1 i f + d2 i f) := by sorry
