-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_eq_avgSub
-- name    : GroundTheory.Automorphic.Parabolic.avgOver_eq_avgSub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:37.18903+00:00
-- url     : https://prove2.me/theorems/253b5d80-8240-4d16-8341-92e40930ef9a
-- title:
--   Parabolic: avg Over eq avg Sub
-- statement:
--   The Parabolic construction uses the avg Over eq avg Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L69-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L69-L94

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

theorem GroundTheory.Automorphic.Parabolic.avgOver_eq_avgSub {S : Subgroup K} (hS : S ≤ (rightStab f).subgroupOf K) (hSi : S.index ≠ 0)
    (x : G) : avgOver K f x = avgSub K S f x := by sorry
