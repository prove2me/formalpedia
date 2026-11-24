-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_relIndex_ne_zero_of_le_right
-- name    : GroundTheory.Automorphic.Parabolic.relIndex_ne_zero_of_le_right
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:33:04.276123+00:00
-- url     : https://prove2.me/theorems/b2733c82-5b13-42d5-9a5c-d3e3089b575a
-- title:
--   Parabolic: rel Index ne zero of le right
-- statement:
--   The Parabolic construction uses the rel Index ne zero of le right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L279-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L279-L284

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

theorem GroundTheory.Automorphic.Parabolic.relIndex_ne_zero_of_le_right {H K K' : Subgroup G} (hKK' : K ≤ K')
    (h : H.relIndex K' ≠ 0) : H.relIndex K ≠ 0 := by sorry
