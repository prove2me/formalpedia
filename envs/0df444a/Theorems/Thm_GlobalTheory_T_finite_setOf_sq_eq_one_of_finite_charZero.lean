-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_setOf_sq_eq_one_of_finite_charZero
-- name    : GlobalTheory.T.finite_setOf_sq_eq_one_of_finite_charZero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:39:47.955804+00:00
-- url     : https://prove2.me/theorems/8f21029a-571c-4159-bad7-6773bcdd8763
-- title:
--   T: finite set Of sq eq one of finite char Zero
-- statement:
--   The T construction uses the finite set Of sq eq one of finite char Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteSqEqOneOfFiniteAlgebraStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteSqEqOneOfFiniteAlgebraStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSqEqOneOfFiniteAlgebra
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSqEqOneOfFiniteAlgebraStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finite_setOf_sq_eq_one_of_finite_charZero : ∀ (k : Type) [Field k] [CharZero k] (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A], Set.Finite {x : A | x ^ 2 = 1} := by sorry
