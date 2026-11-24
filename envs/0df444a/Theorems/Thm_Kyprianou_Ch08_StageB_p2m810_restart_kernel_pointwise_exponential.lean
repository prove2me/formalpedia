-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_restart_kernel_pointwise_exponential
-- name    : Kyprianou.Ch08.StageB.p2m810_restart_kernel_pointwise_exponential
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T21:47:45.419818+00:00
-- url     : https://prove2.me/theorems/ef798d8a-ac08-4362-8891-cddf26fddb2b
-- title:
--   Pointwise exponential payoff after a downcrossing
-- statement:
--   Apply a given nonpositive starting position transform at the finite post-downcrossing state and multiply exponential factors. Both sides vanish at an infinite passage clock.
-- source:
--   Kyprianou (2006), Exercise 8.10(iii)

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m810_restart_kernel_pointwise_exponential
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (q y θ K : ℝ)
    (hrc : ∀ t, ContinuousWithinAt (fun s => X s ω) (Ici t) t)
    (hminus : ∀ x : ℝ, x ≤ 0 →
      (∫ η, discountedAt q (lastExitShifted X x η) ∂P) = K * Real.exp (θ*x)) :
    WithTop.recTopCoe (0 : ℝ) (fun t : ℝ≥0 =>
      Real.exp (-q * (t : ℝ)) *
        (∫ η, discountedAt q (lastExitShifted X (y + X t ω) η) ∂P))
      (tauMinus (shifted X y) 0 ω) = K * downOvershootTilt X q θ y ω := by
  sorry
