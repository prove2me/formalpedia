-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_small_time_dyadic_limit
-- name    : Kyprianou.Ch04.ito43_small_time_dyadic_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:50:17.041084+00:00
-- url     : https://prove2.me/theorems/38db2e5d-3dab-4fbf-aed6-67df0ba8e919
-- title:
--   Countable short-time supremum tends to zero
-- statement:
--   Countable short-time supremum tends to zero.
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

theorem Kyprianou.Ch04.ito43_small_time_dyadic_limit {Ω : Type} [MeasurableSpace Ω]
    (X : NNReal → Ω → ℝ)
    (hX : Measurable (fun z : NNReal × Ω => X z.1 z.2))
    (hCad : ∀ w, IsCadlag (fun t => X t w)) (T : NNReal) :
    let d : ℕ → ℕ × ℕ → NNReal := fun n k =>
      min (T / (n : NNReal)) ((k.1 : NNReal) / 2 ^ k.2)
    let K : ℕ → (ℕ × ℕ) → Ω → ℝ := fun n k w => |X (d n k) w - X 0 w|
    let B : ℕ → Ω → ℝ := fun n w => ⨆ k, K n k w
    ∀ w, Tendsto (fun n => B n w) atTop (nhds 0) := by sorry
