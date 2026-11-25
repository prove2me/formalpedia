-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_rank_equivariantFunctionals_le_one
-- name    : GroundTheory.Automorphic.Whittaker.rank_equivariantFunctionals_le_one
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:08:00.964454+00:00
-- url     : https://prove2.me/theorems/cd8011e7-4d88-4d4a-a239-2226e52f6413
-- title:
--   Whittaker: rank equivariant Functionals le one
-- statement:
--   The Whittaker construction uses the rank equivariant Functionals le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L704-L719
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L704-L719

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

theorem GroundTheory.Automorphic.Whittaker.rank_equivariantFunctionals_le_one (hσ : ∀ x y, σ (x * y) = σ y * σ x)
    (hσμ : μ.map σ = μ) (hGK : BiEquivariantSigmaInvariant H χ σ)
    [TopologicalSpace.SeparableSpace G] (h : IsAdmissible ρ) [ρ.IsIrreducible]
    (hne : equivariantFunctionals (contragredient ρ) (fun g => (χ g)⁻¹) ≠ ⊥) :
    Module.rank ℂ (equivariantFunctionals ρ χ) ≤ 1 := by sorry
