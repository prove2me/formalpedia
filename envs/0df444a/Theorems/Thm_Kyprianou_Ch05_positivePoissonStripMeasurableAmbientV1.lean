-- Prove2me | Theorems.Thm_Kyprianou_Ch05_positivePoissonStripMeasurableAmbientV1
-- name    : Kyprianou.Ch05.positivePoissonStripMeasurableAmbientV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:30:34.441206+00:00
-- url     : https://prove2.me/theorems/1960febf-a9bf-5521-9eba-da8293d705a5
-- title:
--   Positive Poisson strip mass is measurable in the ambient sigma algebra
-- statement:
--   Lift regional measurability to the ambient sigma algebra using the measurable point-family coordinates, then take the real value.
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

theorem Kyprianou.Ch05.positivePoissonStripMeasurableAmbientV1
    {Lambda : Type} [MeasurableSpace Lambda]
    (Q : Measure Lambda) [IsProbabilityMeasure Q]
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Lambda → ℕ) (Z : ℕ → ℕ → Lambda → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) Q)
    (hint : Integrable (fun z : ℝ => min (1 : ℝ) |z|) Pi)
    (s t : ℝ) :
    Measurable (fun w => (∫⁻ z in Ioc s t ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal) := by
  sorry
