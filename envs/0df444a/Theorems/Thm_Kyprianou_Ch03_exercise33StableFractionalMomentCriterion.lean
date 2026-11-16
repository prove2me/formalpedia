-- Prove2me | Theorems.Thm_Kyprianou_Ch03_exercise33StableFractionalMomentCriterion
-- name    : Kyprianou.Ch03.exercise33StableFractionalMomentCriterion
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:51:07.035386+00:00
-- url     : https://prove2.me/theorems/956cf6b0-e112-41f5-8b8b-44ec865fa2ec
-- title:
--   Exercise 3.3(iii): fractional moments of nondegenerate stable Lévy processes
-- statement:
--   Under a genuine nondegenerate alpha-stable Lévy density with positive and negative tails, the eta-th absolute moment exists for all positive times exactly when 0<eta<alpha.
-- source:
--   Kyprianou (2006), Exercise 3.3(iii), p. 84; solution p. 314.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem exercise33StableFractionalMomentCriterion
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
    (∀ t : NNReal, 0 < t →
       Integrable (fun omega => |X t omega| ^ eta) P) ↔ eta < alpha := by
  sorry

end Kyprianou.Ch03
