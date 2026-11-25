-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_distChar_eq_trace
-- name    : GroundTheory.Automorphic.ContragredientTranspose.distChar_eq_trace
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:55:27.003686+00:00
-- url     : https://prove2.me/theorems/1ad20a41-0a08-4348-8125-fff7ab635d2a
-- title:
--   Contragredient Transpose: dist Char eq trace
-- statement:
--   The Contragredient Transpose construction uses the dist Char eq trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/Character.lean#L120-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/Character.lean#L120-L126

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

theorem GroundTheory.Automorphic.ContragredientTranspose.distChar_eq_trace (hρ : IsAdmissible ρ) (f : locallyConstantCompactSupport G ℂ ℂ)
    {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    (hK : ∀ k ∈ K, ∀ x, (f : G → ℂ) (k * x) = (f : G → ℂ) x) :
    distChar μ ρ hρ f = LinearMap.trace ℂ (fixedVectors ρ K) ((heckeLin μ hρ.1 f).restrict
      fun x _ => range_heckeLin_le μ hρ.1 f hK (LinearMap.mem_range_self _ x)) := by sorry
