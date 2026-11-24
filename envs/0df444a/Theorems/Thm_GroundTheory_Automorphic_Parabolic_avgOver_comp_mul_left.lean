-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_comp_mul_left
-- name    : GroundTheory.Automorphic.Parabolic.avgOver_comp_mul_left
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T09:43:23.650642+00:00
-- url     : https://prove2.me/theorems/a9e2f323-8299-4387-981c-c8065dea0254
-- title:
--   Parabolic: avg Over comp mul left
-- statement:
--   The Parabolic construction uses the avg Over comp mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L141-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L141-L154

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
variable {K : Subgroup G} {f : G → W}

theorem GroundTheory.Automorphic.Parabolic.avgOver_comp_mul_left (h x : G) :
    avgOver K (fun y => f (h * y)) x = avgOver K f (h * x) := by sorry
