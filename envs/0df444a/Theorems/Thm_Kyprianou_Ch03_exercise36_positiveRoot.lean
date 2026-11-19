-- Prove2me | Theorems.Thm_Kyprianou_Ch03_exercise36_positiveRoot
-- name    : Kyprianou.Ch03.exercise36_positiveRoot
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T15:46:04.49164+00:00
-- url     : https://prove2.me/theorems/df9338d3-b8fe-4337-af32-95695645effb
-- title:
--   Kyprianou Chapter 3 Exercise 3.6: positive psi root
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

theorem exercise36_positiveRoot
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
    ∃ phi : ℝ, 0 < phi ∧ L.ψ phi = q := by
  sorry

end Kyprianou.Ch03
