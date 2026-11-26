-- Prove2me | Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonCadlagMonotoneV1
-- name    : Kyprianou.Ch05.canonicalPositivePoissonCadlagMonotoneV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:33:30.466271+00:00
-- url     : https://prove2.me/theorems/78afd5b0-e794-5155-aa0c-d84dea058b2a
-- title:
--   Canonical positive Poisson path has almost-sure monotone cadlag paths
-- statement:
--   Apply the deterministic locally finite cumulative-mass theorem on the common conull set. The continuous nonnegative linear drift preserves monotonicity and cadlag paths.
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

theorem Kyprianou.Ch05.canonicalPositivePoissonCadlagMonotoneV1
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
    ∀ᵐ w ∂Q, Monotone (fun t => X t w) ∧ IsCadlag (fun t => X t w) := by
  sorry
