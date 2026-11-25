-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_coeffL_smul_left
-- name    : GroundTheory.Automorphic.Whittaker.coeffL_smul_left
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:06:06.713006+00:00
-- url     : https://prove2.me/theorems/7e42b8a7-d91f-47a8-9fe0-865e52aaf16c
-- title:
--   Whittaker: coeff L smul left
-- statement:
--   The Whittaker construction uses the coeff L smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L306-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L306-L309

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

theorem GroundTheory.Automorphic.Whittaker.coeffL_smul_left (c : ℂ) (ℓ : Module.Dual ℂ V) (f : locallyConstantCompactSupport G ℂ ℂ) :
    coeffL μ hρ (c • ℓ) f = c • coeffL μ hρ ℓ f := by sorry
