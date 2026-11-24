-- Prove2me | Theorems.Thm_Kyprianou_Ch03_expMoment_forward
-- name    : Kyprianou.Ch03.expMoment_forward
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:18:24.86096+00:00
-- url     : https://prove2.me/theorems/ccd8c94e-d87b-4c96-90ae-d5925821c240
-- title:
--   Theorem 3.6, exponential moment versus Levy tail integrability: forward implication
-- statement:
--   One exact logical implication direction of the fully quantified source biconditional; all original quantified hypotheses and endpoint restrictions are retained.
-- source:
--   Kyprianou (2006), Chapter 3, Theorem 3.6, exponential moment versus Levy tail integrability

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem expMoment_forward
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
    ((forall (t : NNReal),
      Integrable (fun omega => Real.exp (beta * X t omega)) P)) -> (IntegrableOn (fun x : Real => Real.exp (beta * x))
        {x : Real | 1 <= abs x} T.levyMeasure) := by
  sorry

end Kyprianou.Ch03
