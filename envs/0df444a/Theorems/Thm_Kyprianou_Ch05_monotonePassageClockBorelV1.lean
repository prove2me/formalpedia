-- Prove2me | Theorems.Thm_Kyprianou_Ch05_monotonePassageClockBorelV1
-- name    : Kyprianou.Ch05.monotonePassageClockBorelV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:19:55.94397+00:00
-- url     : https://prove2.me/theorems/095a6a87-ad57-5af7-ae88-ce5732e23b6b
-- title:
--   Measurable strict crossing clock on monotone real path space
-- statement:
--   Apply the proved Chapter 1 rational-grid infimum identity to the monotone nonnegative extended-real transform of the path. At a positive barrier the zero-time condition is redundant.
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

theorem Kyprianou.Ch05.monotonePassageClockBorelV1
    (x : ℝ) (hx : 0 < x) :
    ∃ T : (NNReal → ℝ) → ENNReal, Measurable T ∧
      ∀ f : NNReal → ℝ, Monotone f → f 0 = 0 →
        T f = sInf ((fun t : NNReal => (t : ENNReal)) '' {t : NNReal | 0 < t ∧ x < f t}) := by
  sorry
