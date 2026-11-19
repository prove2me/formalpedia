-- Prove2me | Theorems.Thm_Kyprianou_Ch03_examples_absoluteMax
-- name    : Kyprianou.Ch03.examples_absoluteMax
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:11:19.776194+00:00
-- url     : https://prove2.me/theorems/dd9ad700-410a-42d5-89a8-baef70e68239
-- title:
--   Exercise 3.3(b) part 3: absoluteMax
-- statement:
--   The full original mathematical subpart 3 of Exercise 3.3(b), with unchanged hypotheses and source conclusion.
-- source:
--   Kyprianou (2006), Chapter 3, Exercise 3.3(b), part 3

import Mathlib
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem examples_absoluteMax :
    IsSubmultiplicative (fun x : ℝ => max |x| 1) := by
  sorry

end Kyprianou.Ch03
