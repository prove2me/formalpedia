-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_mul_right
-- name    : GroundTheory.Automorphic.Parabolic.avgOver_mul_right
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T09:45:08.041983+00:00
-- url     : https://prove2.me/theorems/88d643e2-e3d3-4265-a87a-dc2297089b5c
-- title:
--   Parabolic: avg Over mul right
-- statement:
--   The Parabolic construction uses the avg Over mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L104-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L104-L124

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

theorem GroundTheory.Automorphic.Parabolic.avgOver_mul_right (hf : AvgFinite K f) {k : G} (hk : k ∈ K) (x : G) :
    avgOver K f (x * k) = avgOver K f x := by sorry
