-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_rounded_kernel_pointwise
-- name    : Kyprianou.Ch04.ito43_rounded_kernel_pointwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:51:54.326666+00:00
-- url     : https://prove2.me/theorems/b3acc4c7-e809-5a88-8c8c-82c2dc5673b3
-- title:
--   Pointwise convergence of right-rounded kernel errors
-- statement:
--   Pointwise convergence of right-rounded kernel errors.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_ito43_ceiling_grid_path_limit
import Theorems.Thm_Kyprianou_Ch04_ito43_ceiling_grid
import Theorems.Thm_Kyprianou_Ch04_ito43_compact_kernel_bound
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_rounded_kernel_pointwise {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : Measurable (fun z : NNReal × Omega => X z.1 z.2))
    (hCad : ∀ w, IsCadlag (fun t => X t w))
    (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Ici (0 : ℝ) ×ˢ (univ : Set ℝ))) (T : NNReal) (w : Omega) (hT' : 0 < (T : ℝ)) :
    let R : ℕ → ℝ → ℝ := fun n s => (T : ℝ) * (Nat.ceil (s * (n : ℝ) / (T : ℝ)) : ℝ) / (n : ℝ)
    let F : ℝ → ℝ → ℝ := fun s r =>
      |g (s,X (Real.toNNReal s) w) - g (s,X (Real.toNNReal r) w)|
    let μ := volume.restrict (Icc (0 : ℝ) (T : ℝ))
    ∀ᵐ s ∂μ, Tendsto (fun n => F s (R n s)) atTop (nhds 0) := by sorry
