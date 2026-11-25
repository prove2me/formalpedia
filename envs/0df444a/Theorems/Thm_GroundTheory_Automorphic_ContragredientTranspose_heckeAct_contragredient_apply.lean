-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_heckeAct_contragredient_apply
-- name    : GroundTheory.Automorphic.ContragredientTranspose.heckeAct_contragredient_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:57:15.463979+00:00
-- url     : https://prove2.me/theorems/6260c6d2-3435-4a46-9a70-4de6d6259ef3
-- title:
--   Contragredient Transpose: hecke Act contragredient apply
-- statement:
--   The Contragredient Transpose construction uses the hecke Act contragredient apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/Character.lean#L174-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/Character.lean#L174-L189

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_BiEquivariantSigmaInvariant_inv

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

theorem GroundTheory.Automorphic.ContragredientTranspose.heckeAct_contragredient_apply [μ.IsInvInvariant] (hρ : IsSmooth ρ)
    (f : locallyConstantCompactSupport G ℂ ℂ) (ξ : smoothVectors (Representation.dual ρ)) (v : V) :
    ((heckeAct μ (contragredient ρ) (f : G → ℂ) ξ : smoothVectors (Representation.dual ρ)) :
      Module.Dual ℂ V) v =
      (ξ : Module.Dual ℂ V) (heckeAct μ ρ
        ((compHomeoL (Homeomorph.inv G) f : locallyConstantCompactSupport G ℂ ℂ) : G → ℂ) v) := by sorry
