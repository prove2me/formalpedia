-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_level_primitive_increment
-- name    : Kyprianou.Ch04.kw48_level_primitive_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:38:10.999977+00:00
-- url     : https://prove2.me/theorems/76b4668f-fd47-417c-8d8c-57445b6add87
-- title:
--   Record-level primitive increment
-- statement:
--   Record-level primitive increment.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The difference of two record-level primitives is the integral
over the interval between the two record levels. -/

theorem Kyprianou.Ch04.kw48_level_primitive_increment {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (beta : Real) (w : Ω)
    (a b : NNReal) (hab : a ≤ b) :
    (∫ y in Ioc (runningSup L a w) (runningSup L b w),
      Complex.exp (Complex.I * (beta:Complex) * (y:Complex)) ∂volume) =
      S L beta b w - S L beta a w := by sorry
