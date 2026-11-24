-- Prove2me | Theorems.Thm_GlobalTheory_PowerSeriesNormal_dvd_of_dvd_X_pow_mul
-- name    : GlobalTheory.PowerSeriesNormal.dvd_of_dvd_X_pow_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:53:40.767944+00:00
-- url     : https://prove2.me/theorems/7276624b-e3da-4eeb-a9ff-6b5a2852e24f
-- title:
--   Power Series Normal: dvd of dvd X pow mul
-- statement:
--   The Power Series Normal construction uses the dvd of dvd X pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIntegrallyClosedPowerSeries.lean#L47-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIntegrallyClosedPowerSeries.lean#L47-L60

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

theorem GlobalTheory.PowerSeriesNormal.dvd_of_dvd_X_pow_mul {u a : R⟦X⟧} (hu : ¬ (X : R⟦X⟧) ∣ u) {c : ℕ}
    (h : u ∣ X ^ c * a) : u ∣ a := by sorry
