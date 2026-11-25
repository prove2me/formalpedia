-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_coeffL_convS
-- name    : GroundTheory.Automorphic.Whittaker.coeffL_convS
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:05:09.02484+00:00
-- url     : https://prove2.me/theorems/3a75f146-e102-4b33-9e07-114464ba095a
-- title:
--   Whittaker: coeff L conv S
-- statement:
--   The Whittaker construction uses the coeff L conv S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L224-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L224-L229

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

theorem GroundTheory.Automorphic.Whittaker.coeffL_convS [μ.IsMulRightInvariant] (ℓ : Module.Dual ℂ V) (f₁ f₂ : locallyConstantCompactSupport G ℂ ℂ) :
    coeffL μ hρ ℓ (convS μ f₁ f₂) =
      coeffL μ hρ ((coeffL μ hρ ℓ f₁ : smoothVectors (Representation.dual ρ)) :
        Module.Dual ℂ V) f₂ := by sorry
