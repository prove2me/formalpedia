-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_avgOver
-- name    : GroundTheory.Automorphic.Parabolic.avgOver_avgOver
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T09:43:27.654534+00:00
-- url     : https://prove2.me/theorems/1fe3f503-416e-40ed-abfd-c6b266772e35
-- title:
--   Parabolic: avg Over avg Over
-- statement:
--   The Parabolic construction uses the avg Over avg Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L286-L335
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L286-L335

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

theorem GroundTheory.Automorphic.Parabolic.avgOver_avgOver {K' : Subgroup G} (hKK' : K ≤ K') (hf' : AvgFinite K' f) :
    avgOver K' (avgOver K f) = avgOver K' f := by sorry
