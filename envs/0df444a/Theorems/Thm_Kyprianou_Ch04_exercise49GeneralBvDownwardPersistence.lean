-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49GeneralBvDownwardPersistence
-- name    : Kyprianou.Ch04.exercise49GeneralBvDownwardPersistence
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T22:30:28.702197+00:00
-- url     : https://prove2.me/theorems/626db5db-a1d8-43b6-9264-66a24439392a
-- title:
--   Exercise 4.9(ii): positive probability of initially avoiding downward passage
-- statement:
--   For any bounded-variation Levy process with positive physical drift, excluding subordinators, the first strict downward entrance below zero is not immediate with strictly positive probability. The entrance time is the infimum over positive times, with infinity if there is no entry.
-- source:
--   Kyprianou (2006), first edition, Chapter 4, Exercise 4.9(ii), printed p. 109.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
/-- Source exercise 4.9(ii), printed p. 109. -/
theorem exercise49GeneralBvDownwardPersistence
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (hBV : triplet.gaussianVariance = 0 ∧
      (∫⁻ y in Set.Ioo (-1 : Real) 1,
        ENNReal.ofReal |y| ∂triplet.levyMeasure) < ⊤)
    (drift : Real)
    (hDrift : drift =
       triplet.drift -
         ∫ y in Set.Ioo (-1 : Real) 1, y ∂triplet.levyMeasure)
    (hd : 0 < drift)
    (hNotSubordinator :
      ¬ (∀ᵐ omega : Omega ∂P, Monotone (fun t : NNReal => X t omega))) :
    let tau : Omega -> WithTop NNReal := fun omega =>
      sInf {u : WithTop NNReal |
        ∃ t : NNReal, u = ↑t ∧ 0 < t ∧ X t omega < 0};
    0 < P {omega : Omega | 0 < tau omega} := by
  sorry
end Kyprianou.Ch04
