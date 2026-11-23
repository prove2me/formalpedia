-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_eq_sum_translates
-- name    : GroundTheory.Automorphic.Parabolic.avgOver_eq_sum_translates
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:26.838417+00:00
-- url     : https://prove2.me/theorems/3fc87809-88c2-48c1-a3b4-b073035ed7ea
-- title:
--   Parabolic: avg Over eq sum translates
-- statement:
--   The Parabolic construction uses the avg Over eq sum translates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L246-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L246-L251

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

theorem GroundTheory.Automorphic.Parabolic.avgOver_eq_sum_translates
    [Fintype (K ⧸ (rightStab f).subgroupOf K)] :
    avgOver K f = (((rightStab f).relIndex K : ℂ)⁻¹) •
      ∑ q : K ⧸ (rightStab f).subgroupOf K, fun y => f (y * ((Quotient.out q : K) : G)) := by sorry
