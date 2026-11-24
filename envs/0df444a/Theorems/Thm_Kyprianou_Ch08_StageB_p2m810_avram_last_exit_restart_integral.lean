-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_avram_last_exit_restart_integral
-- name    : Kyprianou.Ch08.StageB.p2m810_avram_last_exit_restart_integral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T22:00:59.850804+00:00
-- url     : https://prove2.me/theorems/eb4b57e4-02ec-4bc8-b5aa-8a7bdae4c71e
-- title:
--   Strong Markov expectation identity at the first strict downcrossing, with the post-passage state as a stopped parameter and a bounded last-exit path reward.
-- statement:
--   Strong Markov expectation identity at the first strict downcrossing, with the post-passage state as a stopped parameter and a bounded last-exit path reward.
-- source:
--   Kyprianou (2006), Exercise 8.10(iii)

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m810_avram_last_exit_restart_integral
    (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (q y : ℝ) (hq : 0 < q) :
    (∫ ω, WithTop.recTopCoe (C := fun _ => ℝ) (0 : ℝ) (fun t : ℝ≥0 =>
      Real.exp (-q * (t : ℝ)) *
        discountedAt q (lastNegativeVisit (fun s (_ : Unit) => y + A.X (t+s) ω) ()))
      (tauMinus (shifted A.X y) 0 ω) ∂P) = (∫ ω, WithTop.recTopCoe (C := fun _ => ℝ) (0 : ℝ) (fun t : ℝ≥0 =>
      Real.exp (-q * (t : ℝ)) *
        (∫ η, discountedAt q (lastExitShifted A.X (y + A.X t ω) η) ∂P))
      (tauMinus (shifted A.X y) 0 ω) ∂P) := by
  sorry
