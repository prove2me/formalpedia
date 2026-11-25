-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DiracComb_eq_mul_comb
-- name    : GlobalTheory.CompanionTheory.DiracComb.eq_mul_comb
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:00:44.472964+00:00
-- url     : https://prove2.me/theorems/8169b4da-c1cb-47ac-b892-21ab15a26ef8
-- title:
--   Dirac Comb: eq mul comb
-- statement:
--   The Dirac Comb construction uses the eq mul comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/DenseHasCompactSupport.lean#L338-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/DenseHasCompactSupport.lean#L338-L428

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

theorem GlobalTheory.CompanionTheory.DiracComb.eq_mul_comb : ∀ (n : ℕ) (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ), (∀ (i : Fin n) (f g : SchwartzMap (Fin n → ℝ) ℂ), (∀ x, g x = cexp (2 * π * I * x i) * f x) → T g = T f) → (∀ (m : Fin n → ℤ) (f g : SchwartzMap (Fin n → ℝ) ℂ), (∀ x, g x = f (x + fun i => (m i : ℝ))) → T g = T f) → ∃ a : ℂ, ∀ f : SchwartzMap (Fin n → ℝ) ℂ, T f = a * ∑' m : Fin n → ℤ, f (fun i => (m i : ℝ)) := by sorry
