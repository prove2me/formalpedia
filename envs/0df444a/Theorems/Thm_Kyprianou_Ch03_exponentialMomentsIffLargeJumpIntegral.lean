-- Prove2me | Theorems.Thm_Kyprianou_Ch03_exponentialMomentsIffLargeJumpIntegral
-- name    : Kyprianou.Ch03.exponentialMomentsIffLargeJumpIntegral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T13:39:21.186702+00:00
-- url     : https://prove2.me/theorems/0e17b884-e265-409b-acb3-069b7d67121f
-- title:
--   Theorem 3.6: exponential moments and Levy measure tails
-- statement:
--   The Levy process with Levy-Khintchine triplet T has finite exponential beta moments at all nonnegative times exactly when exp(beta*x) is integrable against the Levy measure over |x|>=1. Integrable prevents totalising divergent integrals.
-- source:
--   Kyprianou (2006), Chapter 3, Theorem 3.6, pp. 76-78.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem exponentialMomentsIffLargeJumpIntegral
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
    (forall (t : NNReal),
      Integrable (fun omega => Real.exp (beta * X t omega)) P) <->
      IntegrableOn (fun x : Real => Real.exp (beta * x))
        {x : Real | 1 <= abs x} T.levyMeasure := by
  sorry

end Kyprianou.Ch03
