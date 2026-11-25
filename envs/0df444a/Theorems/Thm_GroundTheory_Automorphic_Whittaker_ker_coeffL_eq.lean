-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_ker_coeffL_eq
-- name    : GroundTheory.Automorphic.Whittaker.ker_coeffL_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:08:36.690395+00:00
-- url     : https://prove2.me/theorems/ad612276-e521-48d8-81a9-95fad3f78e28
-- title:
--   Whittaker: ker coeff L eq
-- statement:
--   The Whittaker construction uses the ker coeff L eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L587-L612
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L587-L612

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

theorem GroundTheory.Automorphic.Whittaker.ker_coeffL_eq (h : IsAdmissible ρ) [ρ.IsIrreducible] {ℓ : Module.Dual ℂ V}
    {L : Submodule ℂ (locallyConstantCompactSupport G ℂ ℂ)}
    (hker : LinearMap.ker (coeffL μ h.1 ℓ) ≤ L) (hL : ∀ g, ∀ f ∈ L, rtransL g f ∈ L)
    (hLtop : L ≠ ⊤) : LinearMap.ker (coeffL μ h.1 ℓ) = L := by sorry
