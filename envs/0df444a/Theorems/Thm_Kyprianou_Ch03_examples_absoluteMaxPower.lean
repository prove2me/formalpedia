-- Prove2me | Theorems.Thm_Kyprianou_Ch03_examples_absoluteMaxPower
-- name    : Kyprianou.Ch03.examples_absoluteMaxPower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:11:11.876926+00:00
-- url     : https://prove2.me/theorems/bd0971c8-5d6e-43bd-a085-c569a68c8b67
-- title:
--   Exercise 3.3(b) part 4: absoluteMaxPower
-- statement:
--   The full original mathematical subpart 4 of Exercise 3.3(b), with unchanged hypotheses and source conclusion.
-- source:
--   Kyprianou (2006), Chapter 3, Exercise 3.3(b), part 4

import Mathlib
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem examples_absoluteMaxPower :
    (∀ alpha : ℝ, 0 < alpha →
       IsSubmultiplicative (fun x : ℝ => (max |x| 1) ^ alpha)) := by
  sorry

end Kyprianou.Ch03
