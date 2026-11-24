-- Prove2me | Theorems.Thm_GlobalTheory_PowerSeriesNormal_almostMultiples_le
-- name    : GlobalTheory.PowerSeriesNormal.almostMultiples_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:53:35.592931+00:00
-- url     : https://prove2.me/theorems/e098e998-42b5-4774-aeb4-e7ea2ce3504f
-- title:
--   Power Series Normal: almost Multiples le
-- statement:
--   The Power Series Normal construction uses the almost Multiples le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIntegrallyClosedPowerSeries.lean#L137-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIntegrallyClosedPowerSeries.lean#L137-L167

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

theorem GlobalTheory.PowerSeriesNormal.almostMultiples_le [IsNoetherianRing R] [IsIntegrallyClosed R] {g : R⟦X⟧}
    (hg : ¬ (X : R⟦X⟧) ∣ g) : almostMultiples g ≤ Ideal.span {g} := by sorry
