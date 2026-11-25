-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertDoubling_exists_block
-- name    : GlobalTheory.CompanionTheory.InertDoubling.exists_block
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:01:19.067091+00:00
-- url     : https://prove2.me/theorems/8c60fad5-a654-4100-a9b9-ff4e05c3785d
-- title:
--   Inert Doubling: exists block
-- statement:
--   The Inert Doubling construction uses the exists block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CompletionExists.lean#L113-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CompletionExists.lean#L113-L203

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CompletionExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.Doubling GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertDoubling
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem GlobalTheory.CompanionTheory.InertDoubling.exists_block (hσσ : ∀ x, σ (σ x) = x) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {τ : L} (hτ : τ ∈ intL L)
    (hτ1 : τ + σ τ = 1) {A B U V : Matrix (Fin n) (Fin n) L} (hA : IsInt A) (hB : IsInt B) (hU : IsInt U) (hV : IsInt V)
    (hAB : cT σ A * antiJ L n * A = cT σ B * antiJ L n * B) (hUV : U * A + V * B = 1) :
    ∃ k₀ k₁ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, IsInt k₀ ∧ IsInt k₁ ∧ k₁ * k₀ = 1 ∧
      cT σ k₀ * fromBlocks (antiJ L n) 0 0 (-antiJ L n) * k₀ = fromBlocks (antiJ L n) 0 0 (-antiJ L n) ∧
      k₀.toBlocks₁₁ + k₀.toBlocks₁₂ = A ∧ k₀.toBlocks₂₁ + k₀.toBlocks₂₂ = B := by sorry
