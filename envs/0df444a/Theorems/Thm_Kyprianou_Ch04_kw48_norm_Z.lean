-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_norm_Z
-- name    : Kyprianou.Ch04.kw48_norm_Z
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:32:25.995809+00:00
-- url     : https://prove2.me/theorems/0ad377f2-7d61-4964-aa72-4172001406b2
-- title:
--   Unit modulus of the reflected characteristic exponential
-- statement:
--   Unit modulus of the reflected characteristic exponential.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The two-parameter reflected characteristic exponential has unit norm. -/

theorem Kyprianou.Ch04.kw48_norm_Z {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F)
    (alpha beta : Real) (t : NNReal) (w : Ω) :
    ‖Z L alpha beta t w‖ = 1 := by sorry
