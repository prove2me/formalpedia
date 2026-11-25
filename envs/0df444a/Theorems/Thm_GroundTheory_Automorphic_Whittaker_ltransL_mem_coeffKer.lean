-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_ltransL_mem_coeffKer
-- name    : GroundTheory.Automorphic.Whittaker.ltransL_mem_coeffKer
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:08:19.274322+00:00
-- url     : https://prove2.me/theorems/803467c6-0a9d-4237-965e-41f58e40ebf4
-- title:
--   Whittaker: ltrans L mem coeff Ker
-- statement:
--   The Whittaker construction uses the ltrans L mem coeff Ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L570-L580
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L570-L580

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
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

theorem GroundTheory.Automorphic.Whittaker.ltransL_mem_coeffKer (hρ : IsSmooth ρ)
    {ℓt : Module.Dual ℂ (smoothVectors (Representation.dual ρ))} (a : G)
    {k : locallyConstantCompactSupport G ℂ ℂ} (hk : k ∈ coeffKer μ hρ ℓt) :
    ltransL a k ∈ coeffKer μ hρ ℓt := by sorry
