-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_coeffL_rtransL
-- name    : GroundTheory.Automorphic.Whittaker.coeffL_rtransL
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:02:32.776798+00:00
-- url     : https://prove2.me/theorems/6531fffd-f1d6-4499-9d6a-47b7dcb553bc
-- title:
--   Whittaker: coeff L rtrans L
-- statement:
--   The Whittaker construction uses the coeff L rtrans L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L206-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L206-L213

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

theorem GroundTheory.Automorphic.Whittaker.coeffL_rtransL [μ.IsMulRightInvariant] (ℓ : Module.Dual ℂ V) (g : G) (f : locallyConstantCompactSupport G ℂ ℂ) :
    coeffL μ hρ ℓ (rtransL g f) = contragredient ρ g (coeffL μ hρ ℓ f) := by sorry
