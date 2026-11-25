-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Entire_local_factorisation
-- name    : GlobalTheory.CompanionTheory.Entire.local_factorisation
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:00:42.285466+00:00
-- url     : https://prove2.me/theorems/34e15a06-7349-4745-973b-c3174fcbe14b
-- title:
--   Entire: local factorisation
-- statement:
--   The Entire construction uses the local factorisation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalFactorisationHolomorphic.lean#L7-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalFactorisationHolomorphic.lean#L7-L24

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalFactorisationHolomorphic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Entire

theorem GlobalTheory.CompanionTheory.Entire.local_factorisation :
    ∀ A : ℂ → ℂ, Differentiable ℂ A → (∃ z, A z ≠ 0) → ∀ s₀ : ℂ,
      ∃ (k : ℕ) (U : Set ℂ) (u : ℂ → ℂ), IsOpen U ∧ s₀ ∈ U ∧ DifferentiableOn ℂ u U ∧
        ∀ s ∈ U, u s ≠ 0 ∧ A s = (s - s₀) ^ k * u s := by sorry
