-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_coeffL_zero_left
-- name    : GroundTheory.Automorphic.Whittaker.coeffL_zero_left
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:04:00.753375+00:00
-- url     : https://prove2.me/theorems/3d75fabe-6c76-4852-a652-b03d0f81c064
-- title:
--   Whittaker: coeff L zero left
-- statement:
--   The Whittaker construction uses the coeff L zero left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L311-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L311-L313

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

theorem GroundTheory.Automorphic.Whittaker.coeffL_zero_left (f : locallyConstantCompactSupport G ℂ ℂ) :
    coeffL μ hρ (0 : Module.Dual ℂ V) f = 0 := by sorry
