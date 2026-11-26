-- Prove2me | Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonNoFixedJumpV1
-- name    : Kyprianou.Ch05.canonicalPositivePoissonNoFixedJumpV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:58:57.853903+00:00
-- url     : https://prove2.me/theorems/7ff44047-2603-40b6-8141-c875295f4d57
-- title:
--   The canonical positive process equals its left limit at every fixed positive time almost surely
-- statement:
--   At a deterministic time the Poisson time fibre has zero mass. The proved jump-fibre identity gives zero jump.
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

theorem Kyprianou.Ch05.canonicalPositivePoissonNoFixedJumpV1
    {Lambda : Type} [MeasurableSpace Lambda]
    (Q : Measure Lambda) [IsProbabilityMeasure Q]
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Lambda → ℕ) (Z : ℕ → ℕ → Lambda → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) Q)
    (hint : Integrable (fun z : ℝ => min (1 : ℝ) |z|) Pi)
    (d : ℝ) (hdrift : 0 ≤ d)
    (t : NNReal) (ht : 0 < t) :
    let X := fun (s : NNReal) (w : Lambda) =>
      d * (s : ℝ) + (∫⁻ z in Ioc (0 : ℝ) (s : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal
    ∀ᵐ w ∂Q, Function.leftLim (fun s => X s w) t = X t w := by
  sorry
