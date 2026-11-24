-- Prove2me | Theorems.Thm_GlobalTheory_PowerSeriesNormal_dvd_of_pow_dvd
-- name    : GlobalTheory.PowerSeriesNormal.dvd_of_pow_dvd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:53:54.135627+00:00
-- url     : https://prove2.me/theorems/b096e96b-2bf1-47ae-bf82-4a57557c1d41
-- title:
--   Power Series Normal: dvd of pow dvd
-- statement:
--   The Power Series Normal construction uses the dvd of pow dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIntegrallyClosedPowerSeries.lean#L11-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIntegrallyClosedPowerSeries.lean#L11-L45

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

theorem GlobalTheory.PowerSeriesNormal.dvd_of_pow_dvd [IsNoetherianRing R] [IsIntegrallyClosed R] {f g h : R} (hg : g ≠ 0)
    (hh : h ≠ 0) (H : ∀ n : ℕ, g ^ n ∣ h * f ^ n) : g ∣ f := by sorry
