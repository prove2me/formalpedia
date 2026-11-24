-- Prove2me | Theorems.Thm_Kyprianou_Ch03_exercise36_expTailFormula_positive
-- name    : Kyprianou.Ch03.exercise36_expTailFormula_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:25:35.873654+00:00
-- url     : https://prove2.me/theorems/8f6cb341-363a-4934-8bb1-c48730f77e03
-- title:
--   Chapter 3 Exercise 3.6: positive barrier exponential tail
-- statement:
--   One exact source consequence of the original exponential-clock supremum tail formula under its original assumptions and positive Laplace-exponent root.
-- source:
--   Kyprianou (2006), Chapter 3, Exercise 3.6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LevyExtrema_SBA_runSup
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem exercise36_expTailFormula_positive
{Omega OmegaE : Type}
    [MeasurableSpace Omega] [MeasurableSpace OmegaE]
    (P : Measure Omega) (Q : Measure OmegaE)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂P,
      Antitone (fun t : NNReal => L.X t omega)))
    (q : ℝ) (hq : 0 < q)
    (e : OmegaE → NNReal)
    (hExponential : ∀ t : NNReal,
      (Q {eta : OmegaE | t < e eta}).toReal =
        Real.exp (-q * (t : ℝ))) :
    ∀ (phi : ℝ), (0 < phi ∧ L.ψ phi = q) →
    (∀ x : ℝ, 0 < x →
        ((P.prod Q) {pair : Omega × OmegaE |
          x < LevyExtrema.SBA.runSup
            (fun s => L.X s pair.1) (e pair.2)}).toReal =
        Real.exp (-phi * x)) := by
  sorry

end Kyprianou.Ch03
