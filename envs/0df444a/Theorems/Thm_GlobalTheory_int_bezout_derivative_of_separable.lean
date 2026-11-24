-- Prove2me | Theorems.Thm_GlobalTheory_int_bezout_derivative_of_separable
-- name    : GlobalTheory.int_bezout_derivative_of_separable
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:56:24.018629+00:00
-- url     : https://prove2.me/theorems/f2391f84-74b0-477b-be06-7490486265e7
-- title:
--   Global Theory: int bezout derivative of separable
-- statement:
--   The Global Theory construction uses the int bezout derivative of separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SepIntPolyRootModPrimeSq.lean#L9-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SepIntPolyRootModPrimeSq.lean#L9-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLargePrimeDvdIntPolynomialEvalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SepIntPolyRootModPrimeSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
open GlobalTheory
open Polynomial

theorem GlobalTheory.int_bezout_derivative_of_separable (f : ℤ[X])
    (hf : (f.map (Int.castRingHom ℚ)).Separable) :
    ∃ A B : ℤ[X], ∃ N : ℤ, N ≠ 0 ∧ A * f + B * derivative f = C N := by sorry
