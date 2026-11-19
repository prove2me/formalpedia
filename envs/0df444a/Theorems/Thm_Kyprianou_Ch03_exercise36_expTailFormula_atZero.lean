-- Prove2me | Theorems.Thm_Kyprianou_Ch03_exercise36_expTailFormula_atZero
-- name    : Kyprianou.Ch03.exercise36_expTailFormula_atZero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T17:25:33.6377+00:00
-- url     : https://prove2.me/theorems/accc55b3-9cfe-4f24-9fde-4ac05a144d3d
-- title:
--   Chapter 3 Exercise 3.6: zero barrier exponential tail
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

theorem exercise36_expTailFormula_atZero
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
    ((P.prod Q) {pair : Omega × OmegaE |
          0 < LevyExtrema.SBA.runSup
            (fun s => L.X s pair.1) (e pair.2)}).toReal = 1 := by
  sorry

end Kyprianou.Ch03
