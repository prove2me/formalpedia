-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PrimesAP_linnik_of_relative_model
-- name    : GlobalTheory.CompanionTheory.PrimesAP.linnik_of_relative_model
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:55:33.715443+00:00
-- url     : https://prove2.me/theorems/ebf2f690-871a-4725-914c-2318173f2276
-- title:
--   Primes AP: linnik of relative model
-- statement:
--   The Primes AP construction uses the linnik of relative model property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/PublishedGlobalResults/InvLogIntervalIntegrable.lean#L32-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/PublishedGlobalResults/InvLogIntervalIntegrable.lean#L32-L84

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PrimesAP

theorem GlobalTheory.CompanionTheory.PrimesAP.linnik_of_relative_model (h : PrimesInProgressionsRelative) :
    ∃ L : ℝ, 0 < L ∧ ∀ (N : ℕ) [NeZero N] (a : ZMod N), IsUnit a →
      ∃ p : ℕ, p.Prime ∧ (p : ZMod N) = a ∧ (p : ℝ) ≤ (4 * N : ℝ) ^ L := by sorry
