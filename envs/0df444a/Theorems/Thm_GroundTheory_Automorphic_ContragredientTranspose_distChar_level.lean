-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_distChar_level
-- name    : GroundTheory.Automorphic.ContragredientTranspose.distChar_level
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:48:26.170469+00:00
-- url     : https://prove2.me/theorems/f9bb85d4-9001-4843-962a-a3c9ffa13695
-- title:
--   Contragredient Transpose: dist Char level
-- statement:
--   The Contragredient Transpose construction uses the dist Char level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/Character.lean#L334-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/Character.lean#L334-L339

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
open HeckeAlgebra
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type*} [AddCommGroup V] [Module ℂ V]
  {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))

theorem GroundTheory.Automorphic.ContragredientTranspose.distChar_level {ρ : Representation ℂ G V} (hρ : IsAdmissible ρ)
    (h : HeckeAlgebraLevel μ K hKc hKo) :
    distChar μ ρ hρ (h : HeckeAlgebra μ) = LinearMap.trace ℂ (fixedVectors ρ K) (levelLin hKc hKo ρ h) := by sorry
