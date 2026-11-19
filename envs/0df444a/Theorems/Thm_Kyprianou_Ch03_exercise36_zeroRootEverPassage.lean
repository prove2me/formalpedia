-- Prove2me | Theorems.Thm_Kyprianou_Ch03_exercise36_zeroRootEverPassage
-- name    : Kyprianou.Ch03.exercise36_zeroRootEverPassage
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T15:45:58.519442+00:00
-- url     : https://prove2.me/theorems/1e1166bd-ad2d-4451-8d3b-2b221e0807f8
-- title:
--   Kyprianou Chapter 3 Exercise 3.6: zero-root ever-passage law
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

theorem exercise36_zeroRootEverPassage
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
    (∃ phi0 : ℝ, 0 ≤ phi0 ∧ L.ψ phi0 = 0 ∧
        (∀ theta : ℝ, 0 ≤ theta →
          L.ψ theta = 0 → theta ≤ phi0) ∧
        ∀ x : ℝ, 0 ≤ x →
          (P {omega : Omega |
            ∃ t : NNReal, x < L.X t omega}).toReal =
          Real.exp (-phi0 * x)) := by
  sorry

end Kyprianou.Ch03
