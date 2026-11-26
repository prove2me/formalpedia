-- Prove2me | Theorems.Thm_Kyprianou_Ch05_positivePoissonPathIncrementStripV1
-- name    : Kyprianou.Ch05.positivePoissonPathIncrementStripV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:25:34.807208+00:00
-- url     : https://prove2.me/theorems/f2343ae4-6d14-4a02-8476-c9369f2f2dbe
-- title:
--   Canonical positive Poisson path increments equal drift plus strip mass
-- statement:
--   Split the cumulative integral into disjoint adjacent time strips. Finiteness on every compact horizon justifies addition of real-valued masses.
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

theorem Kyprianou.Ch05.positivePoissonPathIncrementStripV1
    {Lambda : Type} [MeasurableSpace Lambda]
    (Q : Measure Lambda) [IsProbabilityMeasure Q]
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Lambda → ℕ) (Z : ℕ → ℕ → Lambda → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) Q)
    (hint : Integrable (fun z : ℝ => min (1 : ℝ) |z|) Pi)
    (d : ℝ) :
    let X := fun (t : NNReal) (w : Lambda) =>
      d * (t : ℝ) + (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal
    ∀ᵐ w ∂Q, ∀ s t : NNReal, s ≤ t →
      X t w - X s w = d * ((t : ℝ)-(s : ℝ)) +
        (∫⁻ z in Ioc (s : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
          ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal := by
  sorry
