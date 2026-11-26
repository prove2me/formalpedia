-- Prove2me | Theorems.Thm_Kyprianou_Ch05_strictKilledClockFromUnkilledV1
-- name    : Kyprianou.Ch05.strictKilledClockFromUnkilledV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:14:53.951811+00:00
-- url     : https://prove2.me/theorems/ec1fb61d-de2f-581c-a5aa-5d9d5fde9074
-- title:
--   Strict killed crossing clock equals restricted unkilled clock
-- statement:
--   Express the killed crossing set as an intersection with the strict lower interval of the death clock and apply the proved infimum restriction lemma.
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

theorem Kyprianou.Ch05.strictKilledClockFromUnkilledV1
    {Omega : Type} (Y : NNReal → Omega → ℝ) (death : Omega → WithTop NNReal)
    (x : ℝ) (w : Omega) (T : ENNReal)
    (hT : T = sInf ((fun t : NNReal => (t : ENNReal)) '' {t : NNReal | 0 < t ∧ x < Y t w})) :
    (strictUpcrossing Y death x w : ENNReal) =
      if T < (death w : ENNReal) then T else ⊤ := by
  sorry
