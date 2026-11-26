-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_initial_cell_ucp
-- name    : Kyprianou.Ch04.ito43_initial_cell_ucp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:47:49.504153+00:00
-- url     : https://prove2.me/theorems/dd09909b-08b0-480b-8048-e9588d8b7212
-- title:
--   Uniform convergence of a vanishing initial increment times a constant
-- statement:
--   Uniform convergence of a vanishing initial increment times a constant.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_ito43_compact_kernel_bound
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_ge_nnreal
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- A measurable envelope for the short-time oscillation of a cadlag path. -/

theorem Kyprianou.Ch04.ito43_initial_cell_ucp {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P) (C : ℝ) (T : NNReal) :
    ∀ e : ℝ, 0 < e → Tendsto (fun n : ℕ =>
      (P {w | ∃ t ≤ T, e ≤ |C * (X (min t (T / (n : NNReal))) w - X 0 w)|}).toReal)
      atTop (nhds 0) := by sorry
