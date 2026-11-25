-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvUnitMarginalRealExponentialMoment
-- name    : Kyprianou.Ch04.bvUnitMarginalRealExponentialMoment
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T00:30:24.85538+00:00
-- url     : https://prove2.me/theorems/66add565-ed22-46c7-a5a0-4708738a9300
-- title:
--   Bounded-variation Lévy unit marginal: real exponential moment from the triplet
-- statement:
--   The unit marginal of a zero-Gaussian bounded-variation Lévy law has its real exponential moment given by the physical drift and the uncompensated jump exponent when both the marginal exponential and the jump exponential difference are integrable. This isolates a one-dimensional law calculation independent of filtration and the generator localisation in Exercise 4.3.
-- source:
--   Kyprianou (2006), Chapter 4 Exercise 4.3(iv); Lévy–Khintchine formula and finite-variation drift adjustment.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.bvUnitMarginalRealExponentialMoment
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : Omega → Real) (hX : Measurable X)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ theta : Real, charFun (P.map X) theta =
      Complex.exp (Kyprianou.Ch01.levyTripleExponent T theta))
    (hBV : T.gaussianVariance = 0 ∧
      (∫⁻ x in Set.Ioo (-1 : Real) 1,
        ENNReal.ofReal |x| ∂T.levyMeasure) < ⊤)
    (beta : Real)
    (hExp : Integrable (fun omega => Real.exp (beta * X omega)) P)
    (hJump : Integrable (fun x : Real => Real.exp (beta * x) - 1) T.levyMeasure) :
    (∫ omega, Real.exp (beta * X omega) ∂P) =
      Real.exp ((T.drift - ∫ x in Set.Ioo (-1 : Real) 1,
        x ∂T.levyMeasure) * beta +
        ∫ x, (Real.exp (beta * x) - 1) ∂T.levyMeasure) := by
  sorry
