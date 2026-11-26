-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_kernel_full_L1
-- name    : Kyprianou.Ch04.ito43_kernel_full_L1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T12:38:11.248909+00:00
-- url     : https://prove2.me/theorems/89bed7a6-6f5c-55d0-b686-8f4995dcd475
-- title:
--   Full cell continuous-kernel L1 error is measurable and tends to zero
-- statement:
--   Full cell continuous-kernel L1 error is measurable and tends to zero.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_kernel_full_L1 {Omega : Type} [MeasurableSpace Omega]
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
    (∀ n, Measurable (B n)) ∧ ∀ w, Tendsto (fun n => B n w) atTop (nhds 0) := by sorry
