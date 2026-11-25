-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_distChar_biTranslL
-- name    : GroundTheory.Automorphic.ContragredientTranspose.distChar_biTranslL
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:57:27.54128+00:00
-- url     : https://prove2.me/theorems/39032454-2947-448d-b072-ad351e312943
-- title:
--   Contragredient Transpose: dist Char bi Transl L
-- statement:
--   The Contragredient Transpose construction uses the dist Char bi Transl L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/Character.lean#L153-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/Character.lean#L153-L161

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

theorem GroundTheory.Automorphic.ContragredientTranspose.distChar_biTranslL [μ.IsMulRightInvariant] (hρ : IsAdmissible ρ) (g : G)
    (f : locallyConstantCompactSupport G ℂ ℂ) :
    distChar μ ρ hρ (biTranslL g g f) = distChar μ ρ hρ f := by sorry
