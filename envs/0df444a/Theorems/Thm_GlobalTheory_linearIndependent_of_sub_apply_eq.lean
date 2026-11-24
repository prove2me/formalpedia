-- Prove2me | Theorems.Thm_GlobalTheory_linearIndependent_of_sub_apply_eq
-- name    : GlobalTheory.linearIndependent_of_sub_apply_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:07:28.017047+00:00
-- url     : https://prove2.me/theorems/a77251b0-8d30-4fa4-9d16-ee5c86aa8793
-- title:
--   Global Theory: linear Independent of sub apply eq
-- statement:
--   The Global Theory construction uses the linear Independent of sub apply eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DixmierSchurOfRankLeAleph0.lean#L24-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DixmierSchurOfRankLeAleph0.lean#L24-L55

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

theorem GlobalTheory.linearIndependent_of_sub_apply_eq {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (h : ∀ c : ℂ, IsUnit (T - algebraMap ℂ (Module.End ℂ V) c))
    (v : V) (hv : v ≠ 0) (w : ℂ → V)
    (hw : ∀ c, (T - algebraMap ℂ (Module.End ℂ V) c) (w c) = v) :
    LinearIndependent ℂ w := by sorry
