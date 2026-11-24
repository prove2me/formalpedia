-- Prove2me | Theorems.Thm_GlobalTheory_poly_eval_eq_eval_zero_of_eq_inv
-- name    : GlobalTheory.poly_eval_eq_eval_zero_of_eq_inv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:13:52.246057+00:00
-- url     : https://prove2.me/theorems/4b66bf8b-a32b-4c57-bd85-1b1b9cae0c5c
-- title:
--   Global Theory: poly eval eq eval zero of eq inv
-- statement:
--   The Global Theory construction uses the poly eval eq eval zero of eq inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RightInvariantGLOfUpperTriangularRightInvariant.lean#L7-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RightInvariantGLOfUpperTriangularRightInvariant.lean#L7-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RightInvariantGLOfUpperTriangularRightInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory

theorem GlobalTheory.poly_eval_eq_eval_zero_of_eq_inv {k : Type} [Field k] [Infinite k] (p q : k[X]) (c : k)
    (h : ∀ x : k, x ≠ 0 → p.eval x = c * q.eval x⁻¹) : ∀ x : k, p.eval x = p.eval 0 := by sorry
