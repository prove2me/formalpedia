-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PrimesInProgressionsRelativeModel_linnik
-- name    : GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel.linnik
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:02:03.048938+00:00
-- url     : https://prove2.me/theorems/818c38e5-7457-4295-94c6-a61bc5720bb5
-- title:
--   Primes In Progressions Relative Model: linnik
-- statement:
--   The Primes In Progressions Relative Model construction uses the linnik property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/PublishedGlobalResults/InvLogIntervalIntegrable.lean#L135-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/PublishedGlobalResults/InvLogIntervalIntegrable.lean#L135-L139

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

theorem GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel.linnik (h : PrimesInProgressionsRelative) :
    ∃ L : ℝ, ∀ (N : ℕ) [NeZero N] (a : ZMod N), IsUnit a →
      ∃ p : ℕ, p.Prime ∧ (p : ZMod N) = a ∧ (p : ℝ) ≤ (4 * N : ℝ) ^ L := by sorry
