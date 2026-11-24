-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_mul_transvection_apply
-- name    : GroundTheory.Automorphic.mul_transvection_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:35:20.937976+00:00
-- url     : https://prove2.me/theorems/73aa98f3-98d2-49b6-834a-34b474334a01
-- title:
--   Automorphic: mul transvection apply
-- statement:
--   The Automorphic construction uses the mul transvection apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StrongApproximationSLElementary.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StrongApproximationSLElementary.lean#L53-L58

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StrongApproximationSLElementary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GroundTheory GroundTheory.Automorphic
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (n) (R : Type*) [CommRing R]
variable {n R}

theorem GroundTheory.Automorphic.mul_transvection_apply (i j : n) (c : R) (M : Matrix n n R) (a b : n) :
    (M * transvection i j c) a b = if b = j then M a j + c * M a i else M a b := by sorry
