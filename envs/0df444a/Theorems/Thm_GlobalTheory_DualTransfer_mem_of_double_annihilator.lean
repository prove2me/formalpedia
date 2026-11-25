-- Prove2me | Theorems.Thm_GlobalTheory_DualTransfer_mem_of_double_annihilator
-- name    : GlobalTheory.DualTransfer.mem_of_double_annihilator
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:12.624382+00:00
-- url     : https://prove2.me/theorems/c34943a8-8fcb-5831-ad2a-1f00f1bed19e
-- title:
--   Dual Transfer: mem of double annihilator
-- statement:
--   The Dual Transfer construction uses the mem of double annihilator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/DivisiblePontryaginAnnihilatorDuality.lean#L129-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/DivisiblePontryaginAnnihilatorDuality.lean#L129-L192

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_DivisiblePontryaginAnnihilatorDuality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DualTransfer

theorem GlobalTheory.DualTransfer.mem_of_double_annihilator : ∀ {G : Type} [AddCommGroup G] (χ : G → G → ℂ), GlobalTheory.PlaceModel.IsBichar χ → ∀ (X Y L₀ L₀' L : AddSubgroup G), L₀ ≤ X → L₀' ≤ Y → L ≤ X → (∀ u ∈ L₀, ∀ y ∈ L₀', χ u y = 1) → (∀ x ∈ X, (∀ y ∈ L₀', χ x y = 1) → x ∈ L₀) → (∀ y ∈ Y, (∀ u ∈ L₀, χ u y = 1) → y ∈ L₀') → (∀ k : ℕ, 0 < k → ∀ x ∈ X, ∃ x' ∈ X, k • x' = x) → (∀ k : ℕ, 0 < k → ∀ y ∈ Y, ∃ y' ∈ Y, k • y' = y) → (∀ k : ℕ, 0 < k → Function.Injective fun t : G => k • t) → (∀ k : ℕ, 0 < k → ∃ R : Set G, R.Finite ∧ ∀ t ∈ L₀, ∃ r ∈ R, ∃ u ∈ L₀, t = r + k • u) → (∀ k : ℕ, 0 < k → ∃ R : Set G, R.Finite ∧ ∀ t ∈ L₀', ∃ r ∈ R, ∃ u ∈ L₀', t = r + k • u) → ∀ N : ℕ, 0 < N → (∀ u ∈ L₀, N • u ∈ L) → (∀ u ∈ L, N • u ∈ L₀) → ∀ x ∈ X, N • x ∈ L₀ → (∀ y ∈ Y, (∀ u ∈ L, χ u y = 1) → χ x y = 1) → x ∈ L := by sorry
