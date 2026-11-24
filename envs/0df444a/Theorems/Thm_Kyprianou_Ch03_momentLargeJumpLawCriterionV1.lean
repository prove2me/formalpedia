-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentLargeJumpLawCriterionV1
-- name    : Kyprianou.Ch03.momentLargeJumpLawCriterionV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T12:30:27.697739+00:00
-- url     : https://prove2.me/theorems/ac5e6ea6-dc85-4103-bbbf-6b5baebe8d40
-- title:
--   Compound-Poisson marginal submultiplicative moment criterion
-- statement:
--   Large-jump intensity is finite. If it vanishes the marginal is the atom at zero; otherwise the compound-Poisson law is a Poisson mixture of finite iid mark sums. The one-jump term has strictly positive weight, giving necessity, and submultiplicativity bounds the n-jump moment by a geometric sequence in n, summable against Poisson weights.
-- source:
--   Kyprianou (2006), Theorems 3.6 and 3.8; shared reduction of submulMoment_forward and submulMoment_reverse.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.momentLargeJumpLawCriterionV1
    (T : ProbabilityTheory.LevyKhintchineTriple) (t : NNReal) (ht : 0 < t)
    (mu : Measure Real) [IsProbabilityMeasure mu]
    (hmu : ∀ xi : Real, charFun mu xi = Complex.exp (((t : Real) : Complex) *
        ∫ x in {x : Real | 1 ≤ |x|},
          (Complex.exp (Complex.I * (((xi * x : Real) : Complex))) - 1) ∂T.levyMeasure))
    (g : Real → Real) (hg : Kyprianou.Ch03.IsSubmultiplicative g)
    (hg_meas : Measurable g) :
    Integrable g mu ↔ IntegrableOn g {x : Real | 1 ≤ |x|} T.levyMeasure := by sorry
