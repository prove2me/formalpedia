-- Prove2me | Theorems.Thm_GlobalTheory_T_poly_eq_zero_of_newton_recursion
-- name    : GlobalTheory.T.poly_eq_zero_of_newton_recursion
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T09:46:12.75994+00:00
-- url     : https://prove2.me/theorems/401cb743-558c-475a-83df-cb7a540ea04f
-- title:
--   T: poly eq zero of newton recursion
-- statement:
--   The T construction uses the poly eq zero of newton recursion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NewtonRecursionPolyUniqueStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NewtonRecursionPolyUniqueStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NewtonRecursionPolyUnique
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NewtonRecursionPolyUniqueStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.poly_eq_zero_of_newton_recursion : ∀ (m N : ℕ) (p : ℕ → ℂ) (f r : ℂ[X]), m < N → p 0 = (m : ℂ) + 1 → f.natDegree ≤ m → r.natDegree ≤ m → (∀ u : ℂ, (u - m) ^ (N + 1) * (f.eval (u + 1) - f.eval u) - f.eval u * ∑ k ∈ range (N + 1), (-1) ^ k * (u - m) ^ (N - k) * p k = r.eval u) → f = 0 := by sorry
