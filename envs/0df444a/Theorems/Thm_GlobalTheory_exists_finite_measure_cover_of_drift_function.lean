-- Prove2me | Theorems.Thm_GlobalTheory_exists_finite_measure_cover_of_drift_function
-- name    : GlobalTheory.exists_finite_measure_cover_of_drift_function
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:13:08.658221+00:00
-- url     : https://prove2.me/theorems/16df423e-122f-4f93-8057-e72414cc80a5
-- title:
--   Global Theory: exists finite measure cover of drift function
-- statement:
--   The Global Theory construction uses the exists finite measure cover of drift function property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsFiniteMeasureCoverOfDriftFunction.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsFiniteMeasureCoverOfDriftFunction.lean#L12-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasureUnivLeTwoMulSublevelOfDrift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsStrictMeasurableFundamentalSetOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_HaarMapMulRightOfConjInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FundamentalSetLintegralMulRightAndMeasureLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FiniteCovolumeOfDriftFunction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsFiniteMeasureCoverOfDriftFunction
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

theorem GlobalTheory.exists_finite_measure_cover_of_drift_function : (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (Γ : Subgroup G) (σ : Type) [Fintype σ] [Nonempty σ] (h : σ → G) (f : G → ℝ) (c b : ℝ), (∃ U ∈ 𝓝 (1 : G), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → (∀ s, ∃ k : G, k * h s = (h s)⁻¹ * k) → Measurable f → (∀ g, 0 ≤ f g) → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → 0 ≤ c → c < 1 → 0 ≤ b → (∀ g, ∑ s, f (g * h s) ≤ Fintype.card σ * (c * f g + b)) → (∀ M : ℝ, ∃ K : Set G, IsCompact K ∧ ∀ g, f g ≤ M → ∃ γ ∈ Γ, ∃ k ∈ K, g = γ * k) → ∃ Ω : Set G, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : G, ∃ γ ∈ Γ, ∃ w ∈ Ω, g = γ * w) := by sorry
