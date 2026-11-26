-- Prove2me | Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonCharFunV1
-- name    : Kyprianou.Ch05.canonicalPositivePoissonCharFunV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:36:46.868213+00:00
-- url     : https://prove2.me/theorems/c9ecc00d-5cce-53bd-8569-4b730189550e
-- title:
--   Characteristic function of the positive Poisson cumulative path with drift
-- statement:
--   The strip characteristic function is multiplied by the characteristic factor for the constant drift; combine the two exponential factors.
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

theorem Kyprianou.Ch05.canonicalPositivePoissonCharFunV1
    {Lambda : Type} [MeasurableSpace Lambda]
    (Q : Measure Lambda) [IsProbabilityMeasure Q]
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Lambda → ℕ) (Z : ℕ → ℕ → Lambda → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) Q)
    (hint : Integrable (fun z : ℝ => min (1 : ℝ) |z|) Pi)
    (d : ℝ) (t : NNReal) (u : ℝ) :
    charFun (Q.map (fun w => d*(t : ℝ) + (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
      ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal)) u =
      Complex.exp (((t : ℝ) : ℂ) *
        (∫ y in Ioi (0 : ℝ), (Complex.exp (Complex.I * ((u*y : ℝ) : ℂ)) - 1) ∂Pi)
        + ((d*(t : ℝ)*u : ℝ) : ℂ)*Complex.I) := by
  sorry
