-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotentialSurvivalFactorGeneralV1
-- name    : Kyprianou.Ch05.killedPotentialSurvivalFactorGeneralV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:06:27.623+00:00
-- url     : https://prove2.me/theorems/9cf7a03a-eaff-4122-90f3-7e22839d9c3c
-- title:
--   Independent exponential survival factors any measurable nonnegative marginal functional
-- statement:
--   Factor the measurable survival indicator and marginal functional by the specified independence of death and path. Apply the given survival law and map integral formula.
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

theorem Kyprianou.Ch05.killedPotentialSurvivalFactorGeneralV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → ℝ) (death : Omega → WithTop NNReal)
    (eta : ℝ) (hKilled : IsKilledSubordinator P Y death eta)
    (f : ℝ → ENNReal) (hf : Measurable f) (t : ℝ) (ht : 0 ≤ t) :
    (∫⁻ w in {w : Omega | (Real.toNNReal t : WithTop NNReal) < death w},
        f (Y (Real.toNNReal t) w) ∂P) =
    ENNReal.ofReal (Real.exp (-eta*t)) * ∫⁻ v, f v ∂(P.map (Y (Real.toNNReal t))) := by
  sorry
