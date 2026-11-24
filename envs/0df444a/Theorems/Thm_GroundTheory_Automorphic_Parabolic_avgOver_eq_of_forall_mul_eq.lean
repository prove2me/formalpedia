-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_eq_of_forall_mul_eq
-- name    : GroundTheory.Automorphic.Parabolic.avgOver_eq_of_forall_mul_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:32:56.49608+00:00
-- url     : https://prove2.me/theorems/be82b404-e140-4cd7-8459-3831e2426c3b
-- title:
--   Parabolic: avg Over eq of forall mul eq
-- statement:
--   The Parabolic construction uses the avg Over eq of forall mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCount.lean#L22-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCount.lean#L22-L35

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

theorem GroundTheory.Automorphic.Parabolic.avgOver_eq_of_forall_mul_eq {K : Subgroup G} {f : G → W} (hf : AvgFinite K f) {x : G}
    {c : W} (hc : ∀ k ∈ K, f (x * k) = c) : avgOver K f x = c := by sorry
