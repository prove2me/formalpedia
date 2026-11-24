-- Prove2me | Theorems.Thm_Kyprianou_Ch03_expMoment_reverse_positiveTime
-- name    : Kyprianou.Ch03.expMoment_reverse_positiveTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T18:49:30.695487+00:00
-- url     : https://prove2.me/theorems/1a41bce3-2146-46ac-8aed-c8fa5993cddf
-- title:
--   Chapter 3 Levy exponential moments: positive-time criterion from tail Levy integrability
-- statement:
--   Under the original arbitrary Levy process, LK triplet and integrability assumptions, the positive-time exponential moment is integrable for every strictly positive time. The t=0 case follows directly from the Levy process zero-start field.
-- source:
--   Kyprianou (2006) Chapter 3, exponential moment theorem

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem expMoment_reverse_positiveTime
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp ((((t : Real) : Complex)) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (beta : Real) :
    (IntegrableOn (fun x : Real => Real.exp (beta * x))
        {x : Real | 1 <= abs x} T.levyMeasure) -> ((forall (t : NNReal), 0 < t ->
      Integrable (fun omega => Real.exp (beta * X t omega)) P)) := by
  sorry

end Kyprianou.Ch03
