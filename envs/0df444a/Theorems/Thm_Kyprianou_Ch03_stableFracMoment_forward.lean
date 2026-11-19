-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stableFracMoment_forward
-- name    : Kyprianou.Ch03.stableFracMoment_forward
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T13:18:29.527449+00:00
-- url     : https://prove2.me/theorems/a18fe209-d2c3-4c12-ab6e-8ac5b3326dcd
-- title:
--   Exercise 3.3(c), stable fractional moment equivalence: forward implication
-- statement:
--   One exact logical implication direction of the fully quantified source biconditional; all original quantified hypotheses and endpoint restrictions are retained.
-- source:
--   Kyprianou (2006), Chapter 3, Exercise 3.3(c), stable fractional moment equivalence

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem stableFracMoment_forward
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (alpha cPlus cMinus eta : ℝ)
    (hAlpha : 0 < alpha ∧ alpha < 2)
    (hCPlus : 0 ≤ cPlus) (hCMinus : 0 ≤ cMinus)
    (hNonzero : 0 < cPlus + cMinus)
    (hMeasure : T.levyMeasure =
      (volume : Measure ℝ).withDensity
        (fun x : ℝ => ENNReal.ofReal
          (if 0 < x then cPlus / (x ^ (1 + alpha))
           else if x < 0 then cMinus / ((-x) ^ (1 + alpha))
           else 0)))
    (hEta : 0 < eta) :
    ((∀ t : NNReal, 0 < t →
       Integrable (fun omega => |X t omega| ^ eta) P)) -> (eta < alpha) := by
  sorry

end Kyprianou.Ch03
