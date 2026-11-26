-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_exp_product
-- name    : Kyprianou.Ch04.kw48_exp_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:32:23.618792+00:00
-- url     : https://prove2.me/theorems/4d7e76ce-cabc-4ca1-bb2f-77d97c90f211
-- title:
--   Factorisation of the reflected characteristic exponential
-- statement:
--   Factorisation of the reflected characteristic exponential.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Factorise the reflected exponential as the product of the two factors. -/

theorem Kyprianou.Ch04.kw48_exp_product {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (t : NNReal) (w : Ω) :
    E L Psi alpha t w * H L Psi alpha beta t w = Z L alpha beta t w := by sorry
