-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_mem
-- name    : GroundTheory.Automorphic.Parabolic.avgOver_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T09:45:26.692257+00:00
-- url     : https://prove2.me/theorems/8c8e5409-af49-4d3b-aa17-a42914a6e74d
-- title:
--   Parabolic: avg Over mem
-- statement:
--   The Parabolic construction uses the avg Over mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L253-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L253-L259

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Set
variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
  {K : Subgroup G} {f : G → W}

theorem GroundTheory.Automorphic.Parabolic.avgOver_mem (hf : AvgFinite K f) {V : Submodule ℂ (G → W)}
    (hV : ∀ k ∈ K, (fun y => f (y * k)) ∈ V) : avgOver K f ∈ V := by sorry
