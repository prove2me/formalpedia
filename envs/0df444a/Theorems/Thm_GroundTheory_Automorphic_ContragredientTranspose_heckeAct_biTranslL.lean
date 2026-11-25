-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_heckeAct_biTranslL
-- name    : GroundTheory.Automorphic.ContragredientTranspose.heckeAct_biTranslL
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:56:00.938291+00:00
-- url     : https://prove2.me/theorems/1e51fef7-e99c-438a-ba79-efd502b820ac
-- title:
--   Contragredient Transpose: hecke Act bi Transl L
-- statement:
--   The Contragredient Transpose construction uses the hecke Act bi Transl L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/Character.lean#L142-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/Character.lean#L142-L151

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
omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

theorem GroundTheory.Automorphic.ContragredientTranspose.heckeAct_biTranslL [μ.IsMulRightInvariant] (hρ : IsSmooth ρ) (g : G)
    (f : locallyConstantCompactSupport G ℂ ℂ) (v : V) :
    heckeAct μ ρ ((biTranslL g g f : locallyConstantCompactSupport G ℂ ℂ) : G → ℂ) v =
      ρ g (heckeAct μ ρ f (ρ g⁻¹ v)) := by sorry
