-- Prove2me | Theorems.Thm_Kyprianou_Ch03_submulMoment_reverse
-- name    : Kyprianou.Ch03.submulMoment_reverse
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:18:45.439612+00:00
-- url     : https://prove2.me/theorems/7a61b1a8-a560-41d2-a066-3f0a1c5ad126
-- title:
--   Theorem 3.8, submultiplicative moment versus Levy tail integrability: reverse implication
-- statement:
--   One exact logical implication direction of the fully quantified source biconditional; all original quantified hypotheses and endpoint restrictions are retained.
-- source:
--   Kyprianou (2006), Chapter 3, Theorem 3.8, submultiplicative moment versus Levy tail integrability

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem submulMoment_reverse
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp ((((t : Real) : Complex)) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (g : Real -> Real)
    (hg : Kyprianou.Ch03.IsSubmultiplicative g)
    (hg_meas : Measurable g)
    (hg_bounded : forall R : Real, 0 <= R ->
      exists M : Real, forall x : Real, abs x <= R -> g x <= M) :
    ((forall (t : NNReal), 0 < t ->
      Integrable (fun omega => g (X t omega)) P)) -> ((IntegrableOn g {x : Real | 1 <= abs x} T.levyMeasure)) := by
  sorry

end Kyprianou.Ch03
