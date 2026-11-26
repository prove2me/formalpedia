-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_rounded_kernel_bound
-- name    : Kyprianou.Ch04.ito43_rounded_kernel_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:52:03.970665+00:00
-- url     : https://prove2.me/theorems/018255e9-4ed1-4db9-aa31-0234f2bcd997
-- title:
--   Compact bound of right-rounded kernel errors
-- statement:
--   Compact bound of right-rounded kernel errors.
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

theorem Kyprianou.Ch04.ito43_rounded_kernel_bound {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : Measurable (fun z : NNReal × Omega => X z.1 z.2))
    (hCad : ∀ w, IsCadlag (fun t => X t w))
    (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Ici (0 : ℝ) ×ˢ (univ : Set ℝ))) (T : NNReal) (w : Omega) (hT' : 0 < (T : ℝ)) (M : ℝ)
    (hb : ∀ s ∈ Icc (0 : ℝ) (T : ℝ), ∀ r : NNReal, r ≤ T → |g (s,X r w)| ≤ M) :
    let R : ℕ → ℝ → ℝ := fun n s => (T : ℝ) * (Nat.ceil (s * (n : ℝ) / (T : ℝ)) : ℝ) / (n : ℝ)
    let F : ℝ → ℝ → ℝ := fun s r =>
      |g (s,X (Real.toNNReal s) w) - g (s,X (Real.toNNReal r) w)|
    let μ := volume.restrict (Icc (0 : ℝ) (T : ℝ))
    ∀ n : ℕ, 0 < n → ∀ᵐ s ∂μ, ‖F s (R n s)‖ ≤ 2*M := by sorry
