-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_ne_zero_doubleContragredient
-- name    : GroundTheory.Automorphic.Whittaker.exists_ne_zero_doubleContragredient
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:09:26.481256+00:00
-- url     : https://prove2.me/theorems/36901b61-d15f-4da8-90f2-15760cd70b4b
-- title:
--   Whittaker: exists ne zero double Contragredient
-- statement:
--   The Whittaker construction uses the exists ne zero double Contragredient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L747-L774
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L747-L774

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
omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [TopologicalSpace.SeparableSpace G] [MeasurableSpace G] [BorelSpace G]

theorem GroundTheory.Automorphic.Whittaker.exists_ne_zero_doubleContragredient [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [TotallyDisconnectedSpace G] (h : IsAdmissible ρ)
    (hne : equivariantFunctionals ρ χ ≠ ⊥) :
    equivariantFunctionals (contragredient (contragredient ρ)) (fun g => ((χ g)⁻¹)⁻¹) ≠ ⊥ := by sorry
