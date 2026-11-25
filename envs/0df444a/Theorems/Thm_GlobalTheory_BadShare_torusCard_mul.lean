-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_torusCard_mul
-- name    : GlobalTheory.BadShare.torusCard_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:44:41.336804+00:00
-- url     : https://prove2.me/theorems/4d45741b-5e9b-43b7-9fb3-25571775d41a
-- title:
--   Bad Share: torus Card mul
-- statement:
--   The Bad Share construction uses the torus Card mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SamePartIffOfNeZero.lean#L296-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SamePartIffOfNeZero.lean#L296-L299

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime]
variable {g}
open Polynomial Classical
variable (g : ℕ) [Fact g.Prime]
variable {g}

theorem GlobalTheory.BadShare.torusCard_mul {f h : (ZMod g)[X]} (hf : f ≠ 0) (hh : h ≠ 0) :
    _root_.GlobalTheory.BadShare.torusCard g (f * h) = _root_.GlobalTheory.BadShare.torusCard g f * _root_.GlobalTheory.BadShare.torusCard g h := by sorry
