-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_smul_eq
-- name    : GroundTheory.Automorphic.Whittaker.exists_smul_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:08:38.758852+00:00
-- url     : https://prove2.me/theorems/a0651b09-fdf8-499a-97e3-e5e86a8204ff
-- title:
--   Whittaker: exists smul eq
-- statement:
--   The Whittaker construction uses the exists smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L661-L702
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L661-L702

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Filter Topology MeasureTheory
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
variable [μ.IsInvInvariant] {σ : G ≃ₜ G} {H : Subgroup G} {χ : H → ℂ}

theorem GroundTheory.Automorphic.Whittaker.exists_smul_eq (hσ : ∀ x y, σ (x * y) = σ y * σ x) (hσμ : μ.map σ = μ)
    (hGK : BiEquivariantSigmaInvariant H χ σ) [TopologicalSpace.SeparableSpace G]
    (h : IsAdmissible ρ) [ρ.IsIrreducible]
    {ℓt : Module.Dual ℂ (smoothVectors (Representation.dual ρ))}
    (hℓt : ℓt ∈ equivariantFunctionals (contragredient ρ) (fun g => (χ g)⁻¹)) (hℓt0 : ℓt ≠ 0)
    {ℓ₁ ℓ₂ : Module.Dual ℂ V} (h₁ : ℓ₁ ∈ equivariantFunctionals ρ χ) (h₁0 : ℓ₁ ≠ 0)
    (h₂ : ℓ₂ ∈ equivariantFunctionals ρ χ) : ∃ c : ℂ, ℓ₂ = c • ℓ₁ := by sorry
