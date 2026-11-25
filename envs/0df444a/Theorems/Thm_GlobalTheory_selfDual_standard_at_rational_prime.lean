-- Prove2me | Theorems.Thm_GlobalTheory_selfDual_standard_at_rational_prime
-- name    : GlobalTheory.selfDual_standard_at_rational_prime
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:23:28.732102+00:00
-- url     : https://prove2.me/theorems/9fca1003-2c1f-4938-8777-3323a41deedc
-- title:
--   Global Theory: self Dual standard at rational prime
-- statement:
--   The Global Theory construction uses the self Dual standard at rational prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SelfDualLatticeStandardAtRationalPrime.lean#L7-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SelfDualLatticeStandardAtRationalPrime.lean#L7-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SelfDualLatticeStandardAtRationalPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix
open scoped BigOperators
open GlobalTheory

theorem GlobalTheory.selfDual_standard_at_rational_prime : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* K) (n : Type) [Fintype n] [DecidableEq n] (p : ℕ) (𝔭 : HeightOneSpectrum (𝓞 K)) (α β : 𝓞 K) (L : Submodule (𝓞 K) (n → K)) (t : 𝓞 K), (∀ x, σ (σ x) = x) → (∀ x : 𝓞 K, ∃ m : ℤ, (x : K) * σ x = m) → p.Prime → (p : 𝓞 K) ∈ 𝔭.asIdeal → α ∈ 𝔭.asIdeal → β ∉ 𝔭.asIdeal → (β : K) = σ α → (∀ x, x ∈ L ↔ ∀ y ∈ L, ∑ i, x i * σ (y i) ∈ (algebraMap (𝓞 K) K).range) → t ∉ 𝔭.asIdeal → (∀ x ∈ L, ∀ i, (t : K) * x i ∈ (algebraMap (𝓞 K) K).range) → (∀ j, (Pi.single j (t : K) : n → K) ∈ L) → ∃ s : ℕ, Nat.Coprime s p ∧ (∀ x ∈ L, ∀ i, (s : K) * x i ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ v : n → K, (∀ i, v i ∈ (algebraMap (𝓞 K) K).range) → (s : K) • v ∈ L := by sorry
