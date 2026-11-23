-- Prove2me | Theorems.Thm_GlobalTheory_PowerSeriesNormal_exists_eq_X_pow_mul
-- name    : GlobalTheory.PowerSeriesNormal.exists_eq_X_pow_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:01.310088+00:00
-- url     : https://prove2.me/theorems/873a32c4-2998-43bd-a634-866d5807c9ca
-- title:
--   Power Series Normal: exists eq X pow mul
-- statement:
--   The Power Series Normal construction uses the exists eq X pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIntegrallyClosedPowerSeries.lean#L62-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIntegrallyClosedPowerSeries.lean#L62-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegrallyClosedPowerSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.PowerSeriesNormal
open PowerSeries
variable {R : Type} [CommRing R] [IsDomain R]

theorem GlobalTheory.PowerSeriesNormal.exists_eq_X_pow_mul {f : R⟦X⟧} (hf : f ≠ 0) :
    ∃ (a : ℕ) (f₁ : R⟦X⟧), ¬ (X : R⟦X⟧) ∣ f₁ ∧ f = X ^ a * f₁ := by sorry
