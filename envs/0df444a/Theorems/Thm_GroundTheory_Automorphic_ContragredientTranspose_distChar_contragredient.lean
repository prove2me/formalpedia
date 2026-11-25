-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_distChar_contragredient
-- name    : GroundTheory.Automorphic.ContragredientTranspose.distChar_contragredient
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:57:10.012701+00:00
-- url     : https://prove2.me/theorems/48822bfe-061b-4b05-a9cf-b152478d2f43
-- title:
--   Contragredient Transpose: dist Char contragredient
-- statement:
--   The Contragredient Transpose construction uses the dist Char contragredient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/Character.lean#L191-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/Character.lean#L191-L223

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_BiEquivariantSigmaInvariant_inv
import Theorems.Thm_GroundTheory_Automorphic_isAdmissible_contragredient

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

theorem GroundTheory.Automorphic.ContragredientTranspose.distChar_contragredient [μ.IsInvInvariant] (hρ : IsAdmissible ρ)
    (f : locallyConstantCompactSupport G ℂ ℂ) :
    distChar μ (contragredient ρ) (isAdmissible_contragredient hρ) f =
      distChar μ ρ hρ (compHomeoL (Homeomorph.inv G) f) := by sorry
