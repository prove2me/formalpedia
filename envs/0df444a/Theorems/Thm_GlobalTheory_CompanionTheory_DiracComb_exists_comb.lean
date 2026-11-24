-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DiracComb_exists_comb
-- name    : GlobalTheory.CompanionTheory.DiracComb.exists_comb
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:36:58.007203+00:00
-- url     : https://prove2.me/theorems/b6b28dc6-232e-44dd-b1a5-5037e21e5ed2
-- title:
--   Dirac Comb: exists comb
-- statement:
--   The Dirac Comb construction uses the exists comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/DenseHasCompactSupport.lean#L97-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/DenseHasCompactSupport.lean#L97-L122

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

theorem GlobalTheory.CompanionTheory.DiracComb.exists_comb : ∀ (n : ℕ), ∃ S : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ, ∀ f : SchwartzMap (Fin n → ℝ) ℂ, S f = ∑' m : Fin n → ℤ, f (fun i => (m i : ℝ)) := by sorry
