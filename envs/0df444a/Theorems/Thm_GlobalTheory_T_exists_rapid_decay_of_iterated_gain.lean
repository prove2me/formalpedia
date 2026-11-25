-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_rapid_decay_of_iterated_gain
-- name    : GlobalTheory.T.exists_rapid_decay_of_iterated_gain
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:30:51.721069+00:00
-- url     : https://prove2.me/theorems/2c52b8d9-453b-426e-a921-3aeeb9648cd9
-- title:
--   T: exists rapid decay of iterated gain
-- statement:
--   The T construction uses the exists rapid decay of iterated gain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IteratedGainRapidDecayStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IteratedGainRapidDecayStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IteratedGainRapidDecay
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IteratedGainRapidDecayStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_rapid_decay_of_iterated_gain : ∀ (G ι : Type) (B : Finset ι) (q : G → ℝ) (𝓒 : Set (G → ℂ)) (Dr : ι → (G → ℂ) → G → ℂ) (b : ℕ) (C δ₀ : ℝ), 0 < δ₀ → (∀ g, 1 ≤ q g) → (∀ ψ ∈ 𝓒, ∀ i ∈ B, Dr i ψ ∈ 𝓒) → (∀ g, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ q g * δ ^ b ≤ C ∧ (δ₀ ≤ δ ∨ ∃ Ω : Set G, (∀ w ∈ Ω, q w ≤ C * q g ∧ q g ≤ C * q w) ∧ ∀ ψ ∈ 𝓒, ∀ c : ι → ℝ, (∀ i ∈ B, 0 ≤ c i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ c i) → ‖ψ g‖ ≤ C * δ * ∑ i ∈ B, c i)) → ∀ A N : ℕ, ∃ (L : Finset (List ι)) (C' : ℝ), (∀ l ∈ L, ∀ i ∈ l, i ∈ B) ∧ ∀ ψ ∈ 𝓒, ∀ c : List ι → ℝ, (∀ l ∈ L, ∀ g, ‖l.foldr Dr ψ g‖ ≤ c l * q g ^ A) → ∀ g, ‖ψ g‖ * q g ^ N ≤ C' * ∑ l ∈ L, c l := by sorry
