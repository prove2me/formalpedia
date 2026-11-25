-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_smul
-- name    : GroundTheory.Automorphic.Parabolic.avgOver_smul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T09:43:24.049771+00:00
-- url     : https://prove2.me/theorems/a5d28ed5-4734-47de-ae5f-07e303b3572d
-- title:
--   Parabolic: avg Over smul
-- statement:
--   The Parabolic construction uses the avg Over smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L240-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L240-L244

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

theorem GroundTheory.Automorphic.Parabolic.avgOver_smul (c : ℂ) (hf : AvgFinite K f) : avgOver K (c • f) = c • avgOver K f := by sorry
