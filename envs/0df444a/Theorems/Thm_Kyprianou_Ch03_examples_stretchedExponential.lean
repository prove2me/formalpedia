-- Prove2me | Theorems.Thm_Kyprianou_Ch03_examples_stretchedExponential
-- name    : Kyprianou.Ch03.examples_stretchedExponential
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:11:23.12533+00:00
-- url     : https://prove2.me/theorems/d9932a2d-781c-4486-8e9d-f3843a13ffb2
-- title:
--   Exercise 3.3(b) part 5: stretchedExponential
-- statement:
--   The full original mathematical subpart 5 of Exercise 3.3(b), with unchanged hypotheses and source conclusion.
-- source:
--   Kyprianou (2006), Chapter 3, Exercise 3.3(b), part 5

import Mathlib
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem examples_stretchedExponential :
    (∀ beta : ℝ, 0 < beta → beta ≤ 1 →
       IsSubmultiplicative (fun x : ℝ => Real.exp (|x| ^ beta))) := by
  sorry

end Kyprianou.Ch03
