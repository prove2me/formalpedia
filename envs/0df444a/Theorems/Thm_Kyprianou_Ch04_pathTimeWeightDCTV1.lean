-- Prove2me | Theorems.Thm_Kyprianou_Ch04_pathTimeWeightDCTV1
-- name    : Kyprianou.Ch04.pathTimeWeightDCTV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:20:35.435797+00:00
-- url     : https://prove2.me/theorems/7b766135-2c04-450f-8a52-d205636933bf
-- title:
--   Bounded continuous time-state weights pass through path limits
-- statement:
--   Bounded continuous time-state weights pass through path limits.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem pathTimeWeightDCTV1 (Y : ℕ → NNReal → ℝ) (X : NNReal → ℝ)
    (g : ℝ → ℝ → ℝ) (K : ℝ) (T : NNReal)
    (hY : ∀ n, Measurable (Y n)) (hX : Measurable X)
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Ici (0 : ℝ) ×ˢ univ))
    (hK : ∀ s x, 0 ≤ s → |g s x| ≤ K)
    (h : ∀ t : NNReal, 0 < t → t ≤ T →
      Tendsto (fun n => Y n t) atTop (𝓝 (X t))) :
    Tendsto (fun n => ∫ s in Icc (0 : ℝ) (T : ℝ), g s (Y n s.toNNReal)) atTop
      (𝓝 (∫ s in Icc (0 : ℝ) (T : ℝ), g s (X s.toNNReal))) := by
  sorry
end Kyprianou.Ch04
