-- Prove2me | Theorems.Thm_Kyprianou_Ch03_examples_positiveMaxPower
-- name    : Kyprianou.Ch03.examples_positiveMaxPower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:11:16.978224+00:00
-- url     : https://prove2.me/theorems/171deaa0-c576-4f40-b610-d8b940dec60b
-- title:
--   Exercise 3.3(b) part 2: positiveMaxPower
-- statement:
--   The full original mathematical subpart 2 of Exercise 3.3(b), with unchanged hypotheses and source conclusion.
-- source:
--   Kyprianou (2006), Chapter 3, Exercise 3.3(b), part 2

import Mathlib
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem examples_positiveMaxPower :
    (∀ alpha : ℝ, 0 < alpha →
       IsSubmultiplicative (fun x : ℝ => (max x 1) ^ alpha)) := by
  sorry

end Kyprianou.Ch03
