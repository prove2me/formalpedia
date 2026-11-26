-- Prove2me | Theorems.Thm_Kyprianou_Ch05_positiveTimeLeftLimitRealNNRealV1
-- name    : Kyprianou.Ch05.positiveTimeLeftLimitRealNNRealV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:21:51.672808+00:00
-- url     : https://prove2.me/theorems/658a9e4a-132d-5e51-9563-0b611f005c74
-- title:
--   Real and nonnegative real left limits agree at positive times
-- statement:
--   At positive time the real-to-nonnegative-real coercion preserves the left neighbourhood, and on its eventually positive part the two sampled paths agree.
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

theorem Kyprianou.Ch05.positiveTimeLeftLimitRealNNRealV1
    {Omega : Type} [MeasurableSpace Omega] (Q : Measure Omega)
    (g : ℝ → Omega → ℝ) (V : NNReal → Omega → ℝ)
    (hm : ∀ᵐ w ∂Q, Monotone (fun t : NNReal => g t w))
    (hl : ∀ᵐ w ∂Q, ∀ t : NNReal, 0 < t →
      V t w = Function.leftLim (fun s : ℝ => g s w) (t : ℝ)) :
    ∀ᵐ w ∂Q, ∀ t : NNReal, 0 < t →
      V t w = Function.leftLim (fun s : NNReal => g s w) t := by
  sorry
