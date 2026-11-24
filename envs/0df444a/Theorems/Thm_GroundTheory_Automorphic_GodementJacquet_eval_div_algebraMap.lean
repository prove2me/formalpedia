-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_eval_div_algebraMap
-- name    : GroundTheory.Automorphic.GodementJacquet.eval_div_algebraMap
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:08:51.722373+00:00
-- url     : https://prove2.me/theorems/4105d5a2-956f-42fc-81d7-90713d412f7c
-- title:
--   Godement Jacquet: eval div algebra Map
-- statement:
--   The Godement Jacquet construction uses the eval div algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJLaurentIdeal.lean#L66-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJLaurentIdeal.lean#L66-L87

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJLaurentIdeal
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
open GroundTheory.Automorphic.GodementJacquet
open Polynomial

theorem GroundTheory.Automorphic.GodementJacquet.eval_div_algebraMap (P Q : ℂ[X]) {x : ℂ} (hx : Q.eval x ≠ 0) :
    (algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) Q).eval (RingHom.id ℂ) x =
      P.eval x / Q.eval x := by sorry
