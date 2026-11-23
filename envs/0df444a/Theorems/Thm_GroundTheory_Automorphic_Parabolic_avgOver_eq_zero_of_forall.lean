-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_eq_zero_of_forall
-- name    : GroundTheory.Automorphic.Parabolic.avgOver_eq_zero_of_forall
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:40.875654+00:00
-- url     : https://prove2.me/theorems/171bb3d0-4330-41cd-b18a-6e465907bb73
-- title:
--   Parabolic: avg Over eq zero of forall
-- statement:
--   The Parabolic construction uses the avg Over eq zero of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCount.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCount.lean#L17-L20

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

theorem GroundTheory.Automorphic.Parabolic.avgOver_eq_zero_of_forall {K : Subgroup G} {f : G → W} {x : G}
    (h0 : ∀ k ∈ K, f (x * k) = 0) : avgOver K f x = 0 := by sorry
