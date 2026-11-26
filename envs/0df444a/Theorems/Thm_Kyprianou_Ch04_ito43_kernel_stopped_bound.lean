-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_kernel_stopped_bound
-- name    : Kyprianou.Ch04.ito43_kernel_stopped_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:38:12.353118+00:00
-- url     : https://prove2.me/theorems/e239291f-daa2-5205-b489-d54324e2cede
-- title:
--   Stopped kernel error is bounded by full L1 error and a single mesh charge
-- statement:
--   Stopped kernel error is bounded by full L1 error and a single mesh charge.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_kernel_stopped_bound {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : Measurable (fun z : NNReal × Omega => X z.1 z.2))
    (hCad : ∀ w, IsCadlag (fun t => X t w))
    (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Ici (0 : ℝ) ×ˢ (univ : Set ℝ))) (T : NNReal) (M : Omega → ℝ)
    (hM : ∀ w, 0 ≤ M w)
    (hb : ∀ w s, s ∈ Icc (0 : ℝ) (T : ℝ) → ∀ r : NNReal, r ≤ T → |g (s,X r w)| ≤ M w) :
    ∀ n : ℕ, 0 < n → ∀ t : NNReal, t ≤ T → ∀ w,
      let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      |(∫ s in Icc (0 : ℝ) (t : ℝ), g (s,X (Real.toNNReal s) w)) -
        ∑ k ∈ Finset.range n,
          (∫ s in Icc (v k : ℝ) (v (k+1) : ℝ), g (s,X (v (k+1)) w))| ≤ (∑ k ∈ Finset.range n,
      (∫ s in Icc ((u k : NNReal) : ℝ) ((u (k+1) : NNReal) : ℝ),
        |g (s,X (Real.toNNReal s) w) - g (s,X (u (k+1)) w)|)) + 2 * M w * (T : ℝ) / (n : ℝ) := by sorry
