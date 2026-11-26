-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49SafeReservePositiveV1
-- name    : Kyprianou.Ch04.exercise49SafeReservePositiveV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:48:31.495853+00:00
-- url     : https://prove2.me/theorems/8f556a78-3994-5ce8-9107-374703ced700
-- title:
--   A Levy process drifting to infinity has a finite safe reserve with positive probability
-- statement:
--   A Levy process drifting to infinity has a finite safe reserve with positive probability
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49SafeReservePositiveV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hInf : ∀ᵐ ω ∂P, Tendsto (fun t => X t ω) atTop atTop) :
    ∃ n : ℕ, 0 < P {ω | ∀ t : NNReal, -(n : ℝ) ≤ X t ω} := by
  sorry
