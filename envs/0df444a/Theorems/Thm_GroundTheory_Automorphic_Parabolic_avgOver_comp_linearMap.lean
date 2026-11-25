-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_comp_linearMap
-- name    : GroundTheory.Automorphic.Parabolic.avgOver_comp_linearMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:03.497285+00:00
-- url     : https://prove2.me/theorems/24239c3e-372b-4311-a26e-8ed4e6f02fe7
-- title:
--   Parabolic: avg Over comp linear Map
-- statement:
--   The Parabolic construction uses the avg Over comp linear Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L129-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L129-L139

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

theorem GroundTheory.Automorphic.Parabolic.avgOver_comp_linearMap (hf : AvgFinite K f) {W' : Type*} [AddCommGroup W'] [Module ℂ W']
    (T : W →ₗ[ℂ] W') (x : G) :
    avgOver K (fun y => T (f y)) x = T (avgOver K f x) := by sorry
