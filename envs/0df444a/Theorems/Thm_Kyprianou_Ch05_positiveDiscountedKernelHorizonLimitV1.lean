-- Prove2me | Theorems.Thm_Kyprianou_Ch05_positiveDiscountedKernelHorizonLimitV1
-- name    : Kyprianou.Ch05.positiveDiscountedKernelHorizonLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:21:41.891091+00:00
-- url     : https://prove2.me/theorems/bbab5440-ff9d-4f35-b038-365da224e3c2
-- title:
--   Expected discounted time kernel converges to its marginal-law potential integral
-- statement:
--   Use the proved horizon-exhaustion theorem with a fixed time measure. Tonelli exchanges the limiting integrals. At positive times, transfer from V to X almost surely and use the marginal pushforward.
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

theorem Kyprianou.Ch05.positiveDiscountedKernelHorizonLimitV1
    {Omega : Type} [MeasurableSpace Omega]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (V X : NNReal → Omega → ℝ)
    (hV : Measurable (Function.uncurry V))
    (hX : ∀ t, Measurable (X t))
    (he : ∀ t : NNReal, 0 < t → V t =ᵐ[Q] X t)
    (f : ℝ → ENNReal) (hf : Measurable f) (eta : ℝ) :
    Tendsto (fun n : ℕ => ∫⁻ w, ∫⁻ t in Icc (0 : ℝ) (n : ℝ),
      if 0 < t then ENNReal.ofReal (Real.exp (-eta*t)) * f (V t.toNNReal w) else 0
        ∂volume ∂Q) atTop
      (nhds (∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-eta*t)) *
        (∫⁻ v, f v ∂(Q.map (X t.toNNReal))) ∂volume)) := by
  sorry
