-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_small_time_increment_envelope
-- name    : Kyprianou.Ch04.ito43_small_time_increment_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:47:37.852309+00:00
-- url     : https://prove2.me/theorems/0a5479c5-8da3-4ea7-8aad-5db3d61fa6a3
-- title:
--   Measurable vanishing envelope for short-time cadlag path oscillation
-- statement:
--   Measurable vanishing envelope for short-time cadlag path oscillation.
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

theorem Kyprianou.Ch04.ito43_small_time_increment_envelope {Ω : Type} [MeasurableSpace Ω]
    (X : NNReal → Ω → ℝ)
    (hX : Measurable (fun z : NNReal × Ω => X z.1 z.2))
    (hCad : ∀ w, IsCadlag (fun t => X t w)) (T : NNReal) :
    ∃ B : ℕ → Ω → ℝ, (∀ n, Measurable (B n)) ∧
      (∀ w, Tendsto (fun n => B n w) atTop (nhds 0)) ∧
      ∀ (n : ℕ) (w : Ω) (r : NNReal), r ≤ T / (n : NNReal) → |X r w - X 0 w| ≤ B n w := by sorry
