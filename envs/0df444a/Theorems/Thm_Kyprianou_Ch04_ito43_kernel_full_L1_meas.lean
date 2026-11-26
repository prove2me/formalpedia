-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_kernel_full_L1_meas
-- name    : Kyprianou.Ch04.ito43_kernel_full_L1_meas
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:44:37.085197+00:00
-- url     : https://prove2.me/theorems/ac4dd1b0-6adc-426a-8684-05aa0be28515
-- title:
--   Measurability of full-cell continuous-kernel L1 error
-- statement:
--   Measurability of full-cell continuous-kernel L1 error.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_kernel_full_L1_meas {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : Measurable (fun z : NNReal × Omega => X z.1 z.2))
    (hCad : ∀ w, IsCadlag (fun t => X t w))
    (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Ici (0 : ℝ) ×ˢ (univ : Set ℝ))) (T : NNReal) :
    let B : ℕ → Omega → ℝ := fun n w =>
      let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
      (∑ k ∈ Finset.range n,
      (∫ s in Icc ((u k : NNReal) : ℝ) ((u (k+1) : NNReal) : ℝ),
        |g (s,X (Real.toNNReal s) w) - g (s,X (u (k+1)) w)|))
    ∀ n, Measurable (B n) := by sorry
