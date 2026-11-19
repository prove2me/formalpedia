-- Prove2me | Theorems.Thm_Kyprianou_Ch03_examples_singleLog
-- name    : Kyprianou.Ch03.examples_singleLog
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:11:16.938196+00:00
-- url     : https://prove2.me/theorems/da5d1308-3902-4c3a-b77c-d306910fbd86
-- title:
--   Exercise 3.3(b) part 6: singleLog
-- statement:
--   The full original mathematical subpart 6 of Exercise 3.3(b), with unchanged hypotheses and source conclusion.
-- source:
--   Kyprianou (2006), Chapter 3, Exercise 3.3(b), part 6

import Mathlib
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem examples_singleLog :
    IsSubmultiplicative (fun x : ℝ =>
       Real.log (max |x| (Real.exp 1))) := by
  sorry

end Kyprianou.Ch03
