-- Prove2me | Theorems.Thm_GlobalTheory_finite_covolume_of_drift_function
-- name    : GlobalTheory.finite_covolume_of_drift_function
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:46:34.800219+00:00
-- url     : https://prove2.me/theorems/7d49b763-b158-4b6f-adf4-bd9b310fca70
-- title:
--   Global Theory: finite covolume of drift function
-- statement:
--   The Global Theory construction uses the finite covolume of drift function property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FiniteCovolumeOfDriftFunction.lean#L8-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FiniteCovolumeOfDriftFunction.lean#L8-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FiniteCovolumeOfDriftFunction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory

theorem GlobalTheory.finite_covolume_of_drift_function :
    (∀ (Y σ : Type) [MeasurableSpace Y] [Fintype σ] [Nonempty σ] (μ : Measure Y) (R : Y → Y → Prop) (t : σ → Y → Y) (f : Y → ℝ) (c b : ℝ), (∀ s, Measurable (t s)) → (∀ s y y', R y y' → R (t s y) (t s y')) → (∀ φ : Y → ℝ≥0∞, Measurable φ → (∀ y y', R y y' → φ y = φ y') → ∀ s, ∫⁻ y, φ (t s y) ∂μ = ∫⁻ y, φ y ∂μ) → Measurable f → (∀ y, 0 ≤ f y) → (∀ y y', R y y' → f y = f y') → 0 ≤ c → c < 1 → 0 ≤ b → (∀ y, ∑ s, f (t s y) ≤ Fintype.card σ * (c * f y + b)) → ∃ M : ℝ, μ Set.univ ≤ 2 * μ {y | f y ≤ M}) → (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G), (∃ U ∈ 𝓝 (1 : G), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → Countable Γ ∧ ∃ F : Set G, MeasurableSet F ∧ ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ F) → (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (h k : G), k * h = h⁻¹ * k → ν.map (fun g => g * h) = ν) → (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] (F : Set G), MeasurableSet F → (∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ F) → (∀ h : G, ν.map (fun g => g * h) = ν → ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) → ∫⁻ g in F, φ (g * h) ∂ν = ∫⁻ g in F, φ g ∂ν) ∧ ∀ K : Set G, MeasurableSet K → ν (F ∩ {g | ∃ γ ∈ Γ, ∃ k ∈ K, g = γ * k}) ≤ ν K) → (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (Γ : Subgroup G) (σ : Type) [Fintype σ] [Nonempty σ] (h : σ → G) (f : G → ℝ) (c b : ℝ), (∃ U ∈ 𝓝 (1 : G), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → (∀ s, ∃ k : G, k * h s = (h s)⁻¹ * k) → Measurable f → (∀ g, 0 ≤ f g) → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → 0 ≤ c → c < 1 → 0 ≤ b → (∀ g, ∑ s, f (g * h s) ≤ Fintype.card σ * (c * f g + b)) → (∀ M : ℝ, ∃ K : Set G, IsCompact K ∧ ∀ g, f g ≤ M → ∃ γ ∈ Γ, ∃ k ∈ K, g = γ * k) → ∃ Ω : Set G, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : G, ∃ γ ∈ Γ, ∃ w ∈ Ω, g = γ * w) := by sorry
