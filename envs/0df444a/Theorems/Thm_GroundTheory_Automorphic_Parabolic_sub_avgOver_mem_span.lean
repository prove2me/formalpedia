-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_sub_avgOver_mem_span
-- name    : GroundTheory.Automorphic.Parabolic.sub_avgOver_mem_span
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:33:00.644186+00:00
-- url     : https://prove2.me/theorems/a89da0a4-a1d6-4b46-990f-f5abdade8fe6
-- title:
--   Parabolic: sub avg Over mem span
-- statement:
--   The Parabolic construction uses the sub avg Over mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L261-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L261-L277

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

theorem GroundTheory.Automorphic.Parabolic.sub_avgOver_mem_span (hf : AvgFinite K f) :
    f - avgOver K f ∈ Submodule.span ℂ {g | ∃ k ∈ K, g = (fun y => f (y * k)) - f} := by sorry
