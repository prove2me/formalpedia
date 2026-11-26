-- Prove2me | Theorems.Thm_Kyprianou_Ch05_nonnegativeKernelHorizonExhaustionV1
-- name    : Kyprianou.Ch05.nonnegativeKernelHorizonExhaustionV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:50:05.531241+00:00
-- url     : https://prove2.me/theorems/26255ce9-c7c2-5b2f-9b41-0de731efb663
-- title:
--   Monotone convergence of expected restricted nonnegative kernels
-- statement:
--   Apply monotone convergence first to the restricted inner integrals, then to their expectations. The scalar sequence converges to its supremum.
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

theorem Kyprianou.Ch05.nonnegativeKernelHorizonExhaustionV1
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (Q : Measure Omega) (N : Omega → Measure E)
    (g : Omega → E → ENNReal) (hg : ∀ w, Measurable (g w))
    (S : ℕ → Set E) (hS : ∀ n, MeasurableSet (S n)) (hm : Monotone S)
    (hM : ∀ n, AEMeasurable (fun w => ∫⁻ z in S n, g w z ∂N w) Q) :
    Tendsto (fun n : ℕ => ∫⁻ w, ∫⁻ z in S n, g w z ∂N w ∂Q) atTop
      (nhds (∫⁻ w, ∫⁻ z in ⋃ n, S n, g w z ∂N w ∂Q)) := by
  sorry
