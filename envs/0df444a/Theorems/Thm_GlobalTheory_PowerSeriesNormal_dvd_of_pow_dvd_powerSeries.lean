-- Prove2me | Theorems.Thm_GlobalTheory_PowerSeriesNormal_dvd_of_pow_dvd_powerSeries
-- name    : GlobalTheory.PowerSeriesNormal.dvd_of_pow_dvd_powerSeries
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:54:01.963836+00:00
-- url     : https://prove2.me/theorems/a40d8835-49ec-4ac7-b0aa-c518c849b4df
-- title:
--   Power Series Normal: dvd of pow dvd power Series
-- statement:
--   The Power Series Normal construction uses the dvd of pow dvd power Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIntegrallyClosedPowerSeries.lean#L169-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIntegrallyClosedPowerSeries.lean#L169-L197

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

theorem GlobalTheory.PowerSeriesNormal.dvd_of_pow_dvd_powerSeries [IsNoetherianRing R] [IsIntegrallyClosed R] {f g h : R⟦X⟧}
    (hg : g ≠ 0) (hh : h ≠ 0) (H : ∀ n : ℕ, g ^ n ∣ h * f ^ n) : g ∣ f := by sorry
