-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49GeneralBvSmallTimeDrift
-- name    : Kyprianou.Ch04.exercise49GeneralBvSmallTimeDrift
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T22:29:54.803632+00:00
-- url     : https://prove2.me/theorems/fdc529bb-b4bb-4bfd-8c60-7e7aaff9cf6a
-- title:
--   Exercise 4.9(i): general bounded-variation Levy small-time drift limit
-- statement:
--   For any bounded-variation Levy process with positive physical drift d, excluding subordinators, the almost-sure right-hand small-time slope X_t/t tends to d. Both positive and negative jumps are allowed. The conclusion is an actual almost-sure path limit.
-- source:
--   Kyprianou (2006), first edition, Chapter 4, Exercise 4.9(i), printed p. 109.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
/-- Source exercise 4.9(i), printed p. 109. -/
theorem exercise49GeneralBvSmallTimeDrift
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
    ∀ᵐ omega : Omega ∂P,
      Tendsto (fun t : NNReal => X t omega / (t : Real))
        (nhdsWithin (0 : NNReal) (Set.Ioi 0))
        (nhds drift) := by
  sorry
end Kyprianou.Ch04
