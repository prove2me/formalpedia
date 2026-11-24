-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_last_exit_restart_ae_transfer
-- name    : Kyprianou.Ch08.StageB.p2m810_last_exit_restart_ae_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T21:52:40.820351+00:00
-- url     : https://prove2.me/theorems/7d8412c4-4617-4317-a7fa-c1c59e2596fd
-- title:
--   Transfer the exact restart identity through indistinguishable paths, including the inner expectation.
-- statement:
--   Transfer the exact restart identity through indistinguishable paths, including the inner expectation.
-- source:
--   Kyprianou (2006), Exercise 8.10(iii)

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m810_last_exit_restart_ae_transfer
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : ℝ≥0 → Ω → ℝ) (q y : ℝ)
    (hEq : ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω)
    (h : (∫ ω, discountedPositiveLastExit X q y ω ∂P) = (∫ ω, WithTop.recTopCoe (0 : ℝ) (fun t : ℝ≥0 =>
      Real.exp (-q * (t : ℝ)) *
        (∫ η, discountedAt q (lastExitShifted X (y + X t ω) η) ∂P))
      (tauMinus (shifted X y) 0 ω) ∂P)) :
    (∫ ω, discountedPositiveLastExit Y q y ω ∂P) = (∫ ω, WithTop.recTopCoe (0 : ℝ) (fun t : ℝ≥0 =>
      Real.exp (-q * (t : ℝ)) *
        (∫ η, discountedAt q (lastExitShifted Y (y + Y t ω) η) ∂P))
      (tauMinus (shifted Y y) 0 ω) ∂P) := by
  sorry
