-- Prove2me | Theorems.Thm_GlobalTheory_isUnit_aeval_of_forall_isUnit_sub
-- name    : GlobalTheory.isUnit_aeval_of_forall_isUnit_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:01:09.795109+00:00
-- url     : https://prove2.me/theorems/e1812427-e677-4722-9703-ec1a44f0dde3
-- title:
--   Global Theory: is Unit aeval of forall is Unit sub
-- statement:
--   The Global Theory construction uses the is Unit aeval of forall is Unit sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DixmierSchurOfRankLeAleph0.lean#L7-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DixmierSchurOfRankLeAleph0.lean#L7-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DixmierSchurOfRankLeAleph0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.isUnit_aeval_of_forall_isUnit_sub {A : Type*} [Ring A] [Algebra ℂ A] (T : A)
    (h : ∀ c : ℂ, IsUnit (T - algebraMap ℂ A c)) (q : ℂ[X]) (hq : q ≠ 0) :
    IsUnit (aeval T q) := by sorry
