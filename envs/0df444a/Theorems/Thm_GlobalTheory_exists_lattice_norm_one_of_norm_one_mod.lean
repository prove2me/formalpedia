-- Prove2me | Theorems.Thm_GlobalTheory_exists_lattice_norm_one_of_norm_one_mod
-- name    : GlobalTheory.exists_lattice_norm_one_of_norm_one_mod
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:34:10.769394+00:00
-- url     : https://prove2.me/theorems/32b00fe0-ea59-44ab-b352-b67f15d6426d
-- title:
--   Global Theory: exists lattice norm one of norm one mod
-- statement:
--   The Global Theory construction uses the exists lattice norm one of norm one mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HermitianLatticeNormOneOfNormOneModPrime.lean#L5-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HermitianLatticeNormOneOfNormOneModPrime.lean#L5-L135

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HermitianLatticeNormOneOfNormOneModPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_lattice_norm_one_of_norm_one_mod (K V : Type) [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) (p d : ℕ) (θ : K)
    (O : Subring K) (L : AddSubgroup V) (hp : p.Prime) (_hd : d.Prime) (hθ : θ ^ 2 = -(d : K))
    (hσ : σ θ = -θ) (hK : ∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * θ)
    (hOσ : ∀ x ∈ O, σ x ∈ O) (hω : (1 + θ) / 2 ∈ O)
    (hO : ∀ r : ℚ, (r : K) ∈ O ↔ padicNorm p r ≤ 1) (hh : ∀ x y : V, h y x = σ (h x y))
    (_hdef : ∀ x : V, h x x = 0 → x = 0) (hL : ∀ a ∈ O, ∀ x ∈ L, a • x ∈ L)
    (_hint : ∀ x ∈ L, ∀ y ∈ L, h x y ∈ O) (hfull : ∀ x : V, ∃ m : ℕ, (p : K) ^ m • x ∈ L)
    (W : Submodule K V) (he : ∃ e ∈ W, h e e = 1)
    (hy : ∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧ padicNorm p (u - 1) < 1) :
    ∃ z ∈ L, z ∈ W ∧ h z z = 1 := by sorry
