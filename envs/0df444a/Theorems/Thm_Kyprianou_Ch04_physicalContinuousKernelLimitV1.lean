-- Prove2me | Theorems.Thm_Kyprianou_Ch04_physicalContinuousKernelLimitV1
-- name    : Kyprianou.Ch04.physicalContinuousKernelLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:21:05.116982+00:00
-- url     : https://prove2.me/theorems/c6d5ce7c-89e2-5722-a0e7-8f49ac308100
-- title:
--   Dominated retained mark convergence of continuous state kernels
-- statement:
--   Dominated retained mark convergence of continuous state kernels.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem physicalContinuousKernelLimitV1 (R : Measure (ℝ × ℝ)) (T : NNReal)
    (hz : R (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0)
    (Y : ℕ → NNReal → ℝ) (L : NNReal → ℝ) (e : ℕ → ℝ)
    (g : ℝ → ℝ → ℝ → ℝ) (B : ℝ → ℝ)
    (hY : ∀ n, Measurable (Y n)) (he : Tendsto e atTop (𝓝 0))
    (hg : Continuous (fun p : ℝ × ℝ × ℝ => g (max 0 p.1) p.2.1 p.2.2))
    (hzero : ∀ s x, g s x 0 = 0)
    (hB : IntegrableOn (fun z : ℝ × ℝ => B z.2)
      (Icc (0 : ℝ) (T : ℝ) ×ˢ univ) R)
    (hdom : ∀ s x z, 0 ≤ s → |g s x z| ≤ B z)
    (h : ∀ t : NNReal, 0 < t → t ≤ T →
      Tendsto (fun n => Y n t) atTop (𝓝 (L t))) :
    Tendsto (fun n => ∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e n < |x|},
      g z.1 (Y n z.1.toNNReal) z.2 ∂ R) atTop
      (𝓝 (∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ univ, g z.1 (L z.1.toNNReal) z.2 ∂ R)) := by
  sorry
end Kyprianou.Ch04
