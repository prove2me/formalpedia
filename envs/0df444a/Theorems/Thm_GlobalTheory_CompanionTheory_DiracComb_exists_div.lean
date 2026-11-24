-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DiracComb_exists_div
-- name    : GlobalTheory.CompanionTheory.DiracComb.exists_div
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:37:25.530183+00:00
-- url     : https://prove2.me/theorems/9e81934b-1c67-4335-a3ee-9abd1369da3b
-- title:
--   Dirac Comb: exists div
-- statement:
--   The Dirac Comb construction uses the exists div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/DenseHasCompactSupport.lean#L292-L336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/DenseHasCompactSupport.lean#L292-L336

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

theorem GlobalTheory.CompanionTheory.DiracComb.exists_div (n : ℕ) (f : SchwartzMap (Fin n → ℝ) ℂ)
    (hf : tsupport (f : (Fin n → ℝ) → ℂ) ⊆ Metric.ball 0 1) (h0 : f 0 = 0) :
    ∃ g : Fin n → SchwartzMap (Fin n → ℝ) ℂ, (∀ i, HasCompactSupport (g i : (Fin n → ℝ) → ℂ)) ∧
      ∀ x, f x = ∑ i, (cexp (2 * π * I * x i) - 1) * g i x := by sorry
