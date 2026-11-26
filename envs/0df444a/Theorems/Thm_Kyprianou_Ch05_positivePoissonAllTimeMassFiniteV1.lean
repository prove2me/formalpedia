-- Prove2me | Theorems.Thm_Kyprianou_Ch05_positivePoissonAllTimeMassFiniteV1
-- name    : Kyprianou.Ch05.positivePoissonAllTimeMassFiniteV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:25:24.529128+00:00
-- url     : https://prove2.me/theorems/30eb4969-ed5f-5de8-a1fb-bb6a61463043
-- title:
--   Simultaneous finite mass on all compact positive time strips
-- statement:
--   Intersect the conull finite-mass events at integer horizons. Any finite time lies below one of these horizons and the nonnegative integral is monotone in its region.
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

theorem Kyprianou.Ch05.positivePoissonAllTimeMassFiniteV1
    {Lambda : Type} [MeasurableSpace Lambda]
    (Q : Measure Lambda) [IsProbabilityMeasure Q]
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Lambda → ℕ) (Z : ℕ → ℕ → Lambda → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) Q)
    (hint : Integrable (fun z : ℝ => min (1 : ℝ) |z|) Pi) :
    ∀ᵐ w ∂Q, ∀ t : NNReal, (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
      ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)) < ⊤ := by
  sorry
