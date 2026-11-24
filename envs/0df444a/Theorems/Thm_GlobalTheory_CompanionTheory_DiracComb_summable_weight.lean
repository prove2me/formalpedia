-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DiracComb_summable_weight
-- name    : GlobalTheory.CompanionTheory.DiracComb.summable_weight
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:37:13.012583+00:00
-- url     : https://prove2.me/theorems/cac15d69-9221-4770-a321-45f76b5f96e8
-- title:
--   Dirac Comb: summable weight
-- statement:
--   The Dirac Comb construction uses the summable weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/DenseHasCompactSupport.lean#L68-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/DenseHasCompactSupport.lean#L68-L95

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_DenseHasCompactSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped Real ContDiff
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DiracComb

theorem GlobalTheory.CompanionTheory.DiracComb.summable_weight (n : ℕ) :
    Summable fun m : Fin n → ℤ => ((1 + ‖(fun i => (m i : ℝ))‖) ^ (2 * n))⁻¹ := by sorry
