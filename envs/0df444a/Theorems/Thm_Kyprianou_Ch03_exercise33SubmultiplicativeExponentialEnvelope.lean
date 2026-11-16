-- Prove2me | Theorems.Thm_Kyprianou_Ch03_exercise33SubmultiplicativeExponentialEnvelope
-- name    : Kyprianou.Ch03.exercise33SubmultiplicativeExponentialEnvelope
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:50:17.964569+00:00
-- url     : https://prove2.me/theorems/a2702f26-4260-48cb-a98f-a4d37c0ab10f
-- title:
--   Exercise 3.3(i): submultiplicative functions have an exponential envelope
-- statement:
--   Exercise 3.3(i), mathematical exponential envelope used in Theorem 3.8. The original full moment equivalence remains a separately certified theorem.
-- source:
--   Kyprianou (2006), Exercise 3.3(i), p. 83; solution p. 313.

import Mathlib
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem exercise33SubmultiplicativeExponentialEnvelope
(g : ℝ → ℝ)
    (hg : IsSubmultiplicative g)
    (hgBounded : ∀ R : ℝ, 0 ≤ R →
       ∃ M : ℝ, ∀ x, |x| ≤ R → g x ≤ M) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
       ∀ x : ℝ, g x ≤ a * Real.exp (b * |x|) := by
  sorry

end Kyprianou.Ch03
