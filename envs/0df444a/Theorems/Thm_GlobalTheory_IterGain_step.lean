-- Prove2me | Theorems.Thm_GlobalTheory_IterGain_step
-- name    : GlobalTheory.IterGain.step
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:22:44.245792+00:00
-- url     : https://prove2.me/theorems/7797f17c-70e0-4155-9533-80bd9b5747dc
-- title:
--   Iter Gain: step
-- statement:
--   The Iter Gain construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IteratedGainRapidDecay.lean#L36-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IteratedGainRapidDecay.lean#L36-L145

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IteratedGainRapidDecay
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.IterGain

theorem GlobalTheory.IterGain.step {G ι : Type} [DecidableEq ι] (B : Finset ι) (q : G → ℝ) (𝓒 : Set (G → ℂ))
    (Dr : ι → (G → ℂ) → G → ℂ) (m : ℕ) (C δ₀ K : ℝ) (Q : G → ℝ) (A : ℕ)
    (hm : m ≠ 0) (hδ₀ : 0 < δ₀) (hC : 1 ≤ C) (hK : 1 ≤ K) (hKm : K ^ m = C)
    (hq : ∀ g, 1 ≤ q g) (hQ1 : ∀ g, 1 ≤ Q g) (hQm : ∀ g, Q g ^ m = q g)
    (hcl : ∀ ψ ∈ 𝓒, ∀ i ∈ B, Dr i ψ ∈ 𝓒)
    (hgain : ∀ g, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ q g * δ ^ m ≤ C ∧ (δ₀ ≤ δ ∨ ∃ Ω : Set G,
      (∀ w ∈ Ω, q w ≤ C * q g ∧ q g ≤ C * q w) ∧ ∀ ψ ∈ 𝓒, ∀ c : ι → ℝ,
        (∀ i ∈ B, 0 ≤ c i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ c i) → ‖ψ g‖ ≤ C * δ * ∑ i ∈ B, c i))
    (k : ℕ) : ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ ψ ∈ 𝓒, ∀ c : List ι → ℝ, (∀ l ∈ words B k, 0 ≤ c l) →
      (∀ l ∈ words B k, ∀ g, ‖l.foldr Dr ψ g‖ ≤ c l * q g ^ A) →
      ∀ g, ‖ψ g‖ * Q g ^ k ≤ Ck * q g ^ A * ∑ l ∈ words B k, c l := by sorry
