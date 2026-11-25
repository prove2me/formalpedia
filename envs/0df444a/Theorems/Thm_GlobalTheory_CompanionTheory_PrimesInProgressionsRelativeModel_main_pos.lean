-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PrimesInProgressionsRelativeModel_main_pos
-- name    : GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel.main_pos
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:01:53.901063+00:00
-- url     : https://prove2.me/theorems/4e55871f-2b72-4b04-9f91-25cb40c61c27
-- title:
--   Primes In Progressions Relative Model: main pos
-- statement:
--   The Primes In Progressions Relative Model construction uses the main pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/PublishedGlobalResults/InvLogIntervalIntegrable.lean#L111-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/PublishedGlobalResults/InvLogIntervalIntegrable.lean#L111-L120

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

theorem GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel.main_pos {X Y θ : ℝ} (hθ : θ ≤ 1) (hY : 2 ≤ Y) (hYX : Y < X) :
    0 < (∫ t in (2 : ℝ)..X, 1 / Real.log t) - θ * ∫ t in (2 : ℝ)..Y, 1 / Real.log t := by sorry
