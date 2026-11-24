-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DiracComb_exists_partition
-- name    : GlobalTheory.CompanionTheory.DiracComb.exists_partition
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:36:43.713307+00:00
-- url     : https://prove2.me/theorems/a32f4e25-28fa-495e-a9a5-6723e0d2bd2f
-- title:
--   Dirac Comb: exists partition
-- statement:
--   The Dirac Comb construction uses the exists partition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/DenseHasCompactSupport.lean#L141-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/DenseHasCompactSupport.lean#L141-L162

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

theorem GlobalTheory.CompanionTheory.DiracComb.exists_partition : ∀ (n : ℕ) (f : SchwartzMap (Fin n → ℝ) ℂ), HasCompactSupport (f : (Fin n → ℝ) → ℂ) → ∃ (s : Finset (Fin n → ℤ)) (g : (Fin n → ℤ) → SchwartzMap (Fin n → ℝ) ℂ), (∀ m, tsupport (g m : (Fin n → ℝ) → ℂ) ⊆ Metric.ball (fun i => (m i : ℝ)) 1) ∧ f = ∑ m ∈ s, g m := by sorry
