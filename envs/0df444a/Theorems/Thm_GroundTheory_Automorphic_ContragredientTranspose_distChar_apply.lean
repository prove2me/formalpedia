-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_distChar_apply
-- name    : GroundTheory.Automorphic.ContragredientTranspose.distChar_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:55:20.908745+00:00
-- url     : https://prove2.me/theorems/67e1475c-2844-4a17-bdf3-a8503c6d96a3
-- title:
--   Contragredient Transpose: dist Char apply
-- statement:
--   The Contragredient Transpose construction uses the dist Char apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/Character.lean#L117-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/Character.lean#L117-L118

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character
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
open GroundTheory.Automorphic.ContragredientTranspose
open Set Filter Topology MeasureTheory Module Whittaker
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

theorem GroundTheory.Automorphic.ContragredientTranspose.distChar_apply (hρ : IsAdmissible ρ) (f : locallyConstantCompactSupport G ℂ ℂ) :
    distChar μ ρ hρ f = finTrace (heckeLin μ hρ.1 f) := by sorry
