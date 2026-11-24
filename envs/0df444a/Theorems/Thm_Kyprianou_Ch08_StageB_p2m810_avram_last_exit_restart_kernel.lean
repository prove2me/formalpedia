-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_avram_last_exit_restart_kernel
-- name    : Kyprianou.Ch08.StageB.p2m810_avram_last_exit_restart_kernel
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T21:52:41.775499+00:00
-- url     : https://prove2.me/theorems/65cd4596-65ea-4f12-ae9f-3019f75387d0
-- title:
--   Last-exit restart kernel for the all-path right-continuous Avram model.
-- statement:
--   Last-exit restart kernel for the all-path right-continuous Avram model.
-- source:
--   Kyprianou (2006), Exercise 8.10(iii)

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m810_avram_last_exit_restart_kernel
    (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (q y : ℝ) (hq : 0 < q) (hy : 0 < y)
    (hDrift : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 => A.X t ω) atTop atTop) :
    (∫ ω, discountedPositiveLastExit A.X q y ω ∂P) = (∫ ω, WithTop.recTopCoe (0 : ℝ) (fun t : ℝ≥0 =>
      Real.exp (-q * (t : ℝ)) *
        (∫ η, discountedAt q (lastExitShifted A.X (y + A.X t ω) η) ∂P))
      (tauMinus (shifted A.X y) 0 ω) ∂P) := by
  sorry
