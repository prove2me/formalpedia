-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_eq_sum
-- name    : GroundTheory.Automorphic.Parabolic.avgOver_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:02.276662+00:00
-- url     : https://prove2.me/theorems/7f615545-bc91-4d6a-abb6-3af5ff92484c
-- title:
--   Parabolic: avg Over eq sum
-- statement:
--   The Parabolic construction uses the avg Over eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L98-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L98-L102

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

theorem GroundTheory.Automorphic.Parabolic.avgOver_eq_sum [Fintype (K ⧸ (rightStab f).subgroupOf K)] (x : G) :
    avgOver K f x = (((rightStab f).relIndex K : ℂ)⁻¹) •
      ∑ q : K ⧸ (rightStab f).subgroupOf K, f (x * ((Quotient.out q : K) : G)) := by sorry
