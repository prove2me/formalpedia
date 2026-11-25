-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_coeffL_apply
-- name    : GroundTheory.Automorphic.Whittaker.coeffL_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:00:58.502366+00:00
-- url     : https://prove2.me/theorems/78dcaa80-f34e-4a60-99b1-e8c2a2818b04
-- title:
--   Whittaker: coeff L apply
-- statement:
--   The Whittaker construction uses the coeff L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L202-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L202-L204

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
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
variable (hρ : IsSmooth ρ)
include hρ

theorem GroundTheory.Automorphic.Whittaker.coeffL_apply [μ.IsMulRightInvariant] (ℓ : Module.Dual ℂ V) (f : locallyConstantCompactSupport G ℂ ℂ) (v : V) :
    ((coeffL μ hρ ℓ f : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) v =
      ℓ (heckeAct μ ρ f v) := by sorry
