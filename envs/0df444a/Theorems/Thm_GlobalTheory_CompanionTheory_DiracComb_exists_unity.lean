-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DiracComb_exists_unity
-- name    : GlobalTheory.CompanionTheory.DiracComb.exists_unity
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:36:50.288028+00:00
-- url     : https://prove2.me/theorems/6241727f-f45b-44b2-a029-e09d7461817a
-- title:
--   Dirac Comb: exists unity
-- statement:
--   The Dirac Comb construction uses the exists unity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/DenseHasCompactSupport.lean#L124-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/DenseHasCompactSupport.lean#L124-L139

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

theorem GlobalTheory.CompanionTheory.DiracComb.exists_unity (n : ℕ) : ∃ ρ : (Fin n → ℤ) → (Fin n → ℝ) → ℝ, (∀ m, ContDiff ℝ ∞ (ρ m)) ∧
    (∀ m, tsupport (ρ m) ⊆ Metric.ball (fun i => (m i : ℝ)) 1) ∧
    LocallyFinite (fun m => Function.support (ρ m)) ∧ ∀ x, ∑ᶠ m, ρ m x = 1 := by sorry
