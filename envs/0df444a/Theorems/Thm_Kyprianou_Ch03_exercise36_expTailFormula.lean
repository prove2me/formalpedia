-- Prove2me | Theorems.Thm_Kyprianou_Ch03_exercise36_expTailFormula
-- name    : Kyprianou.Ch03.exercise36_expTailFormula
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T15:46:00.181182+00:00
-- url     : https://prove2.me/theorems/552419d9-a9de-402b-8507-50b3612c8d03
-- title:
--   Kyprianou Chapter 3 Exercise 3.6: exponential supremum tail formula
-- statement:
--   One complete independent obligation from Exercise 3.6, preserving the original process and exponential-horizon assumptions. Any conditional tail obligation uses the same positive root as the root-existence child.
-- source:
--   Kyprianou (2006), Chapter 3, Exercise 3.6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LevyExtrema_SBA_runSup
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem exercise36_expTailFormula
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
    (∀ x : ℝ, 0 ≤ x →
        ((P.prod Q) {pair : Omega × OmegaE |
          x < LevyExtrema.SBA.runSup
            (fun s => L.X s pair.1) (e pair.2)}).toReal =
        Real.exp (-phi * x)) := by
  sorry

end Kyprianou.Ch03
