-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_kernel_joint_ucp
-- name    : Kyprianou.Ch04.ito43_kernel_joint_ucp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:36:19.193416+00:00
-- url     : https://prove2.me/theorems/8821b489-5bb2-543c-abe0-9bb1564edc3b
-- title:
--   Uniform stopped continuous-kernel convergence for jointly measurable cadlag paths
-- statement:
--   Uniform stopped continuous-kernel convergence for a jointly measurable family of everywhere cadlag paths.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_kernel_joint_ucp {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : Measurable (fun z : NNReal × Omega => X z.1 z.2))
    (hCad : ∀ w, IsCadlag (fun t => X t w))
    (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Ici (0 : ℝ) ×ˢ (univ : Set ℝ))) :
    ∀ (T : NNReal) (e : ℝ), 0 < e →
      Tendsto (fun n : ℕ =>
        (P {w | ∃ t : NNReal, t ≤ T ∧
          let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
          let v : ℕ → NNReal := fun k => min t (u k)
          e ≤ |(∫ s in Icc (0 : ℝ) (t : ℝ), g (s,X (Real.toNNReal s) w)) -
            ∑ k ∈ Finset.range n,
              (∫ s in Icc (v k : ℝ) (v (k+1) : ℝ), g (s,X (v (k+1)) w))|}).toReal)
        atTop (nhds 0) := by sorry
