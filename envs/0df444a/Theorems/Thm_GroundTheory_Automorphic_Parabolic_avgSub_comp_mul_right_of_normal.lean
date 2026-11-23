-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgSub_comp_mul_right_of_normal
-- name    : GroundTheory.Automorphic.Parabolic.avgSub_comp_mul_right_of_normal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:34.847098+00:00
-- url     : https://prove2.me/theorems/2d717cf4-a2b2-48e4-8fd0-4b989fb8a0c6
-- title:
--   Parabolic: avg Sub comp mul right of normal
-- statement:
--   The Parabolic construction uses the avg Sub comp mul right of normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L163-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L163-L182

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

theorem GroundTheory.Automorphic.Parabolic.avgSub_comp_mul_right_of_normal {S : Subgroup K} [S.Normal] (hSi : S.index ≠ 0)
    (hS : S ≤ (rightStab f).subgroupOf K) {k : G} (hk : k ∈ K) (x : G) :
    avgSub K S (fun y => f (y * k)) x = avgSub K S f x := by sorry
