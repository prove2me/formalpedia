-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_mul_left_eq
-- name    : GroundTheory.Automorphic.Parabolic.avgOver_mul_left_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:36.556532+00:00
-- url     : https://prove2.me/theorems/b31227df-5d6f-4450-8e0d-77e525fa7ee9
-- title:
--   Parabolic: avg Over mul left eq
-- statement:
--   The Parabolic construction uses the avg Over mul left eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCount.lean#L164-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCount.lean#L164-L170

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCount
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
variable {A : Subgroup G}
variable (θ : A → W →ₗ[ℂ] W)

theorem GroundTheory.Automorphic.Parabolic.avgOver_mul_left_eq {K : Subgroup G} {h : G → W}
    (hh : ∀ a : A, ∀ y, h ((a : G) * y) = θ a (h y)) (hf : AvgFinite K h) (a : A) (y : G) :
    avgOver K h ((a : G) * y) = θ a (avgOver K h y) := by sorry
