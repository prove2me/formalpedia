-- Prove2me | Theorems.Thm_Kyprianou_Ch03_examples_positiveMax
-- name    : Kyprianou.Ch03.examples_positiveMax
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:11:25.515878+00:00
-- url     : https://prove2.me/theorems/54b7a8b4-068b-4ded-a625-85b87a24b9c8
-- title:
--   Exercise 3.3(b) part 1: positiveMax
-- statement:
--   The full original mathematical subpart 1 of Exercise 3.3(b), with unchanged hypotheses and source conclusion.
-- source:
--   Kyprianou (2006), Chapter 3, Exercise 3.3(b), part 1

import Mathlib
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem examples_positiveMax :
    IsSubmultiplicative (fun x : ℝ => max x 1) := by
  sorry

end Kyprianou.Ch03
