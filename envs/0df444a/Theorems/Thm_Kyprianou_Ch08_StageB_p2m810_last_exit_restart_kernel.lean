-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_last_exit_restart_kernel
-- name    : Kyprianou.Ch08.StageB.p2m810_last_exit_restart_kernel
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T19:39:44.25826+00:00
-- url     : https://prove2.me/theorems/71e4a94c-ea8a-4059-b58f-9241d4cb1e84
-- title:
--   Last exit restart kernel at first negative passage
-- statement:
--   Starting at y>0, the discounted positive last-exit transform factors through the first finite negative passage and the ordinary last-exit transform from the random post-passage position.
-- source:
--   Kyprianou (2006), Exercise 8.10(iii), strong Markov step

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m810_last_exit_restart_kernel
    (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (q y : ℝ)
    (hq : 0 < q) (hy : 0 < y)
    (hDrift : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 => D.X t ω) atTop atTop) :
    (∫ ω, discountedPositiveLastExit D.X q y ω ∂P) =
      ∫ ω, WithTop.recTopCoe (0 : ℝ) (fun t : ℝ≥0 =>
        Real.exp (-q * (t : ℝ)) *
          (∫ η, discountedAt q (lastExitShifted D.X (y + D.X t ω) η) ∂P))
        (tauMinus (shifted D.X y) 0 ω) ∂P := by
  sorry
