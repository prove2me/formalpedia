-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_rank_mul_rank_le_one
-- name    : GroundTheory.Automorphic.Whittaker.rank_mul_rank_le_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:08:58.8856+00:00
-- url     : https://prove2.me/theorems/b2db719e-b83e-496b-81ef-da6ae9cebc67
-- title:
--   Whittaker: rank mul rank le one
-- statement:
--   The Whittaker construction uses the rank mul rank le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L776-L794
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L776-L794

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
  [T2Space G] [TotallyDisconnectedSpace G] [TopologicalSpace.SeparableSpace G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {σ : G ≃ₜ G} {H : Subgroup G} {χ : H → ℂ}

theorem GroundTheory.Automorphic.Whittaker.rank_mul_rank_le_one (hσ : ∀ x y, σ (x * y) = σ y * σ x) (hσμ : μ.map σ = μ)
    (hGK : BiEquivariantSigmaInvariant H χ σ) (h : IsAdmissible ρ) [ρ.IsIrreducible] :
    Module.rank ℂ (equivariantFunctionals ρ χ) *
      Module.rank ℂ (equivariantFunctionals (contragredient ρ) (fun g => (χ g)⁻¹)) ≤ 1 := by sorry
