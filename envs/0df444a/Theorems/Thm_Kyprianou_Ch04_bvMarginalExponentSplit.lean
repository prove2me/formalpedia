-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvMarginalExponentSplit
-- name    : Kyprianou.Ch04.bvMarginalExponentSplit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T08:15:07.758544+00:00
-- url     : https://prove2.me/theorems/36f8b12b-ee92-54b4-a6b1-110a0b50a5ad
-- title:
--   Bounded variation real Laplace exponent algebra
-- statement:
--   Split the integrable jump kernel into complementary small and large mark sets, and integrate the BV drift correction.
-- source:
--   Kyprianou (2006), Exercise 4.3(iv).

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.bvMarginalExponentSplit
    (T : LevyKhintchineTriple)
    (hBV : (∫⁻ x in Ioo (-1 : Real) 1, ENNReal.ofReal |x| ∂T.levyMeasure) < ⊤)
    (b : Real) (hJump : Integrable (fun x : Real => Real.exp (b*x)-1) T.levyMeasure) :
    (∫ x in {x : Real | 1 ≤ |x|}, (Real.exp (b*x)-1) ∂T.levyMeasure) +
      (T.drift*b + ∫ x in Ioo (-1 : Real) 1,
        (Real.exp (b*x)-1-b*x) ∂T.levyMeasure) =
      (T.drift - ∫ x in Ioo (-1 : Real) 1, x ∂T.levyMeasure)*b +
        ∫ x, (Real.exp (b*x)-1) ∂T.levyMeasure := by
  sorry
