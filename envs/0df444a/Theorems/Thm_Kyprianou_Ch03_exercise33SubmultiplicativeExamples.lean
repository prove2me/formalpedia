-- Prove2me | Theorems.Thm_Kyprianou_Ch03_exercise33SubmultiplicativeExamples
-- name    : Kyprianou.Ch03.exercise33SubmultiplicativeExamples
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:50:39.266199+00:00
-- url     : https://prove2.me/theorems/73b672fe-32ad-4d71-90ce-db100b1d03fc
-- title:
--   Exercise 3.3(ii): all seven submultiplicative example families
-- statement:
--   All seven examples. Interpret ambiguous fractional powers for negative x using (max x 1)^alpha, ensuring the real-valued function is defined everywhere.
-- source:
--   Kyprianou (2006), Exercise 3.3(ii), p. 84; solution p. 314.

import Mathlib
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem exercise33SubmultiplicativeExamples :
IsSubmultiplicative (fun x : ℝ => max x 1) ∧
    (∀ alpha : ℝ, 0 < alpha →
       IsSubmultiplicative (fun x : ℝ => (max x 1) ^ alpha)) ∧
    IsSubmultiplicative (fun x : ℝ => max |x| 1) ∧
    (∀ alpha : ℝ, 0 < alpha →
       IsSubmultiplicative (fun x : ℝ => (max |x| 1) ^ alpha)) ∧
    (∀ beta : ℝ, 0 < beta → beta ≤ 1 →
       IsSubmultiplicative (fun x : ℝ => Real.exp (|x| ^ beta))) ∧
    IsSubmultiplicative (fun x : ℝ =>
       Real.log (max |x| (Real.exp 1))) ∧
    IsSubmultiplicative (fun x : ℝ =>
       Real.log (Real.log (max |x| (Real.exp (Real.exp 1))))) := by
  sorry

end Kyprianou.Ch03
