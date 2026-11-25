-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_add
-- name    : GroundTheory.Automorphic.Parabolic.avgOver_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T09:42:09.526128+00:00
-- url     : https://prove2.me/theorems/a77785ff-1fa3-4801-8410-9fe5cf7f9372
-- title:
--   Parabolic: avg Over add
-- statement:
--   The Parabolic construction uses the avg Over add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L223-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L223-L238

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

theorem GroundTheory.Automorphic.Parabolic.avgOver_add {g : G → W} (hf : AvgFinite K f) (hg : AvgFinite K g) :
    avgOver K (f + g) = avgOver K f + avgOver K g := by sorry
