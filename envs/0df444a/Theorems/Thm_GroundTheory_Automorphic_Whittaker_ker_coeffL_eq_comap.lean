-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_ker_coeffL_eq_comap
-- name    : GroundTheory.Automorphic.Whittaker.ker_coeffL_eq_comap
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:08:13.9376+00:00
-- url     : https://prove2.me/theorems/3ca35c50-3247-48e1-8b0d-944c38149827
-- title:
--   Whittaker: ker coeff L eq comap
-- statement:
--   The Whittaker construction uses the ker coeff L eq comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L616-L659
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L616-L659

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

theorem GroundTheory.Automorphic.Whittaker.ker_coeffL_eq_comap (hσ : ∀ x y, σ (x * y) = σ y * σ x) (hσμ : μ.map σ = μ)
    (hGK : BiEquivariantSigmaInvariant H χ σ) (h : IsAdmissible ρ) [ρ.IsIrreducible]
    {ℓ : Module.Dual ℂ V} (hℓ : ℓ ∈ equivariantFunctionals ρ χ) (hℓ0 : ℓ ≠ 0)
    {ℓt : Module.Dual ℂ (smoothVectors (Representation.dual ρ))}
    (hℓt : ℓt ∈ equivariantFunctionals (contragredient ρ) (fun g => (χ g)⁻¹)) (hℓt0 : ℓt ≠ 0) :
    LinearMap.ker (coeffL μ h.1 ℓ) = (coeffKer μ h.1 ℓt).comap (compHomeoL σ) := by sorry
