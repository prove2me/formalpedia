-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgSub_eq_sum
-- name    : GroundTheory.Automorphic.Parabolic.avgSub_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:33.788809+00:00
-- url     : https://prove2.me/theorems/f183bab6-2083-4610-afa7-9dd05fdac865
-- title:
--   Parabolic: avg Sub eq sum
-- statement:
--   The Parabolic construction uses the avg Sub eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L63-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L63-L65

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

theorem GroundTheory.Automorphic.Parabolic.avgSub_eq_sum (K : Subgroup G) (S : Subgroup K) [Fintype (K ⧸ S)] (f : G → W) (x : G) :
    avgSub K S f x = ((S.index : ℂ)⁻¹) • ∑ q : K ⧸ S, f (x * ((Quotient.out q : K) : G)) := by sorry
