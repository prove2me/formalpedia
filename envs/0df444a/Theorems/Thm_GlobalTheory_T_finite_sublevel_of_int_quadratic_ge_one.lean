-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_sublevel_of_int_quadratic_ge_one
-- name    : GlobalTheory.T.finite_sublevel_of_int_quadratic_ge_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:31:08.105824+00:00
-- url     : https://prove2.me/theorems/4c45cdb2-58b7-5691-bfc5-56d62fa91e07
-- title:
--   T: finite sublevel of int quadratic ge one
-- statement:
--   The T construction uses the finite sublevel of int quadratic ge one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteSublevelOfIntQuadraticGeOneStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteSublevelOfIntQuadraticGeOneStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteSublevelOfIntQuadraticGeOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteSublevelOfIntQuadraticGeOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finite_sublevel_of_int_quadratic_ge_one : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (q : X → ℤ), (∀ a, q (-a) = q a) → (∀ a a' b, q (a + a' + b) + q a + q a' + q b = q (a + a') + q (a + b) + q (a' + b)) → (∀ a, a ≠ 0 → 1 ≤ q a) → ∀ N : ℤ, {a | q a ≤ N}.Finite := by sorry
