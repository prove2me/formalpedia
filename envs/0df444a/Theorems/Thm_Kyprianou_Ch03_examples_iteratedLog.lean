-- Prove2me | Theorems.Thm_Kyprianou_Ch03_examples_iteratedLog
-- name    : Kyprianou.Ch03.examples_iteratedLog
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:11:16.488956+00:00
-- url     : https://prove2.me/theorems/3110812a-86ff-4674-a301-65cee2fe98df
-- title:
--   Exercise 3.3(b) part 7: iteratedLog
-- statement:
--   The full original mathematical subpart 7 of Exercise 3.3(b), with unchanged hypotheses and source conclusion.
-- source:
--   Kyprianou (2006), Chapter 3, Exercise 3.3(b), part 7

import Mathlib
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem examples_iteratedLog :
    IsSubmultiplicative (fun x : ℝ =>
       Real.log (Real.log (max |x| (Real.exp (Real.exp 1))))) := by
  sorry

end Kyprianou.Ch03
