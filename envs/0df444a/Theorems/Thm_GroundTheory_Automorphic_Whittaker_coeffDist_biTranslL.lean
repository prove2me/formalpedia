-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_coeffDist_biTranslL
-- name    : GroundTheory.Automorphic.Whittaker.coeffDist_biTranslL
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:04:51.366268+00:00
-- url     : https://prove2.me/theorems/aa4fcfb6-2aa2-4925-b1dc-f299514a048e
-- title:
--   Whittaker: coeff Dist bi Transl L
-- statement:
--   The Whittaker construction uses the coeff Dist bi Transl L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L328-L335
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L328-L335

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
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ)

theorem GroundTheory.Automorphic.Whittaker.coeffDist_biTranslL {H : Subgroup G} {χ : H → ℂ} {ℓ : Module.Dual ℂ V}
    (hℓ : ℓ ∈ equivariantFunctionals ρ χ)
    {ℓt : Module.Dual ℂ (smoothVectors (Representation.dual ρ))}
    (hℓt : ℓt ∈ equivariantFunctionals (contragredient ρ) (fun h => (χ h)⁻¹))
    (f : locallyConstantCompactSupport G ℂ ℂ) (h₁ h₂ : H) :
    coeffDist μ hρ ℓ ℓt (biTranslL (h₁ : G) (h₂ : G) f) = χ h₁ * (χ h₂)⁻¹ * coeffDist μ hρ ℓ ℓt f := by sorry
