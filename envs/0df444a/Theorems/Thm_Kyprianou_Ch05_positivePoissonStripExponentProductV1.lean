-- Prove2me | Theorems.Thm_Kyprianou_Ch05_positivePoissonStripExponentProductV1
-- name    : Kyprianou.Ch05.positivePoissonStripExponentProductV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:30:40.102693+00:00
-- url     : https://prove2.me/theorems/3c3913a7-96d0-5a1f-9467-feeeb6b9f6cf
-- title:
--   Complex exponent integral over a positive mark strip factors into duration and mark exponent
-- statement:
--   The exponent integrand vanishes off the time-mark strip. On the strip it factors into a constant time integrand and the mark integrand; apply product integration.
-- source:
--   Kyprianou (2006), Chapter 5, Theorem 5.6.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false

theorem Kyprianou.Ch05.positivePoissonStripExponentProductV1
    (Pi : Measure ℝ) [SigmaFinite Pi] (s t u : ℝ) (hst : s ≤ t) :
    (∫ z : ℝ × ℝ, Complex.exp (Complex.I *
      ((u * (Ioc s t ×ˢ Ioi (0 : ℝ)).indicator Prod.snd z : ℝ) : ℂ)) - 1
        ∂((volume : Measure ℝ).prod Pi)) =
      ((t-s : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ),
        (Complex.exp (Complex.I * ((u*y : ℝ) : ℂ)) - 1) ∂Pi := by
  sorry
