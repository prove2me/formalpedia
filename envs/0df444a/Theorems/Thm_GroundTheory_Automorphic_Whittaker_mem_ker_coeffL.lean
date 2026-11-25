-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_mem_ker_coeffL
-- name    : GroundTheory.Automorphic.Whittaker.mem_ker_coeffL
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:54:52.27682+00:00
-- url     : https://prove2.me/theorems/80585d35-5156-5074-979b-c2692b9fc79f
-- title:
--   Whittaker: mem ker coeff L
-- statement:
--   The Whittaker construction uses the mem ker coeff L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L582-L585
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L582-L585

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

theorem GroundTheory.Automorphic.Whittaker.mem_ker_coeffL (hρ : IsSmooth ρ) {ℓ : Module.Dual ℂ V}
    {f : locallyConstantCompactSupport G ℂ ℂ} :
    f ∈ LinearMap.ker (coeffL μ hρ ℓ) ↔ coeffL μ hρ ℓ f = 0 := by sorry
