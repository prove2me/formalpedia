-- Prove2me | Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonJumpFibreV1
-- name    : Kyprianou.Ch05.canonicalPositivePoissonJumpFibreV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:58:58.97298+00:00
-- url     : https://prove2.me/theorems/a9ceff19-7f51-4def-a387-17585c858607
-- title:
--   The canonical positive process jump equals the mass of its time fibre
-- statement:
--   The increment strip identity holds simultaneously at all times. Take its left-hand limit, using continuity of the drift and the shrinking-strip mass theorem.
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

theorem Kyprianou.Ch05.canonicalPositivePoissonJumpFibreV1
    {Lambda : Type} [MeasurableSpace Lambda]
    (Q : Measure Lambda) [IsProbabilityMeasure Q]
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Lambda → ℕ) (Z : ℕ → ℕ → Lambda → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) Q)
    (hint : Integrable (fun z : ℝ => min (1 : ℝ) |z|) Pi)
    (d : ℝ) (hdrift : 0 ≤ d) :
    let X := fun (t : NNReal) (w : Lambda) =>
      d * (t : ℝ) + (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal
    ∀ᵐ w ∂Q, ∀ t : NNReal, 0 < t →
      X t w - Function.leftLim (fun s => X s w) t =
        (∫⁻ z in {(t : ℝ)} ×ˢ Ioi (0 : ℝ), ENNReal.ofReal z.2
          ∂(poissonRandomMeasure K Z w)).toReal := by
  sorry
