-- Prove2me | Theorems.Thm_Kyprianou_Ch05_positivePoissonStripCharacteristicV1
-- name    : Kyprianou.Ch05.positivePoissonStripCharacteristicV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:30:47.530797+00:00
-- url     : https://prove2.me/theorems/66204626-ce2e-5b6e-83af-12193bad5de3
-- title:
--   Characteristic function of an arbitrary positive Poisson strip
-- statement:
--   Apply Chapter 2's Poisson integral law to the marked strip indicator, use its truncated integrability, and factor the resulting complex exponent.
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

theorem Kyprianou.Ch05.positivePoissonStripCharacteristicV1
    {Lambda : Type} [MeasurableSpace Lambda]
    (Q : Measure Lambda) [IsProbabilityMeasure Q]
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Lambda → ℕ) (Z : ℕ → ℕ → Lambda → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) Q)
    (hint : Integrable (fun z : ℝ => min (1 : ℝ) |z|) Pi)
    (s t u : ℝ) (hst : s ≤ t) :
    charFun (Q.map (fun w => (∫⁻ z in Ioc s t ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal)) u =
      Complex.exp (((t-s : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ),
        (Complex.exp (Complex.I * ((u*y : ℝ) : ℂ)) - 1) ∂Pi) := by
  sorry
