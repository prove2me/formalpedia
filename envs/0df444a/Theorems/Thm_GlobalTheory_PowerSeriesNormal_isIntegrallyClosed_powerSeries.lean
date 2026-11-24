-- Prove2me | Theorems.Thm_GlobalTheory_PowerSeriesNormal_isIntegrallyClosed_powerSeries
-- name    : GlobalTheory.PowerSeriesNormal.isIntegrallyClosed_powerSeries
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:53:56.653799+00:00
-- url     : https://prove2.me/theorems/5da20a07-1e53-4b37-bd6b-bf5eacc7aeab
-- title:
--   Power Series Normal: is Integrally Closed power Series
-- statement:
--   The Power Series Normal construction uses the is Integrally Closed power Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIntegrallyClosedPowerSeries.lean#L199-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIntegrallyClosedPowerSeries.lean#L199-L239

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

theorem GlobalTheory.PowerSeriesNormal.isIntegrallyClosed_powerSeries : ∀ (R : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R], IsIntegrallyClosed (PowerSeries R) := by sorry
