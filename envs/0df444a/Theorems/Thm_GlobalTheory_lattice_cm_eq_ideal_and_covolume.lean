-- Prove2me | Theorems.Thm_GlobalTheory_lattice_cm_eq_ideal_and_covolume
-- name    : GlobalTheory.lattice_cm_eq_ideal_and_covolume
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:02:25.059794+00:00
-- url     : https://prove2.me/theorems/d80e63da-90ab-42f1-a1d6-a25767ee685c
-- title:
--   Global Theory: lattice cm eq ideal and covolume
-- statement:
--   The Global Theory construction uses the lattice cm eq ideal and covolume property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/LatticeCmEqIdealAndCovolume.lean#L208-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/LatticeCmEqIdealAndCovolume.lean#L208-L275

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex NumberField Module
open scoped nonZeroDivisors
open GlobalTheory
open CMLattice

theorem GlobalTheory.lattice_cm_eq_ideal_and_covolume :
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (σ : K →+* ℂ), ¬ NumberField.ComplexEmbedding.IsReal σ →
  ∀ (L L' : PeriodPair), (∀ (a : 𝓞 K), ∀ z ∈ L.lattice, σ (a : K) * z ∈ L.lattice) →
  (∃ (𝔞 : Ideal (𝓞 K)) (c : ℂ), 𝔞 ≠ ⊥ ∧ c ≠ 0 ∧ ∀ z, z ∈ L.lattice ↔ ∃ a ∈ 𝔞, z = c * σ (a : K)) ∧
  ∀ (𝔟 : Ideal (𝓞 K)) (β : ℂ), 𝔟 ≠ ⊥ → β ≠ 0 →
    (∀ x : K, (∀ b ∈ 𝔟, IsIntegral ℤ (x * (b : K))) → ∀ z ∈ L.lattice, β * σ x * z ∈ L'.lattice) →
    (∀ y ∈ 𝔟, ∀ z ∈ L'.lattice, β⁻¹ * σ (y : K) * z ∈ L.lattice) →
    (∀ z, z ∈ L'.lattice ↔ ∀ y ∈ 𝔟, β⁻¹ * σ (y : K) * z ∈ L.lattice) ∧
    |(L'.ω₁ * starRingEnd ℂ L'.ω₂).im| * Ideal.absNorm 𝔟 = ‖β‖ ^ 2 * |(L.ω₁ * starRingEnd ℂ L.ω₂).im| := by sorry
