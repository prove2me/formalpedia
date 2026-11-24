-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PrimesInProgressionsRelativeModel_invLog_intervalIntegrable
-- name    : GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel.invLog_intervalIntegrable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:29.187194+00:00
-- url     : https://prove2.me/theorems/6fce554b-6f9d-474f-a30d-ee30eb091d47
-- title:
--   Primes In Progressions Relative Model: inv Log interval Integrable
-- statement:
--   The Primes In Progressions Relative Model construction uses the inv Log interval Integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/PublishedGlobalResults/InvLogIntervalIntegrable.lean#L96-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/PublishedGlobalResults/InvLogIntervalIntegrable.lean#L96-L102

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_PublishedTheorems_PublishedGlobalResults_PrimesInProgressionsRelative
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_PrimesInProgressionsRelativeOfTzRat
import Definitions.Def_Development_AutomorphicSpectrum_PublishedTheorems_PublishedGlobalResults_InvLogIntervalIntegrable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel

theorem GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel.invLog_intervalIntegrable {u v : ℝ} (hu : 2 ≤ u) (hv : 2 ≤ v) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume u v := by sorry
