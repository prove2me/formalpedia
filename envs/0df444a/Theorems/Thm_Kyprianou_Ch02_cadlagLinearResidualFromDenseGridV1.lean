-- Prove2me | Theorems.Thm_Kyprianou_Ch02_cadlagLinearResidualFromDenseGridV1
-- name    : Kyprianou.Ch02.cadlagLinearResidualFromDenseGridV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:15:52.97007+00:00
-- url     : https://prove2.me/theorems/02c04f55-7518-4eed-9d1f-87fc8316d093
-- title:
--   Extend a linear signed-jump residual from dense times
-- statement:
--   Use the locally absolutely summable cumulative jump-series right continuity and right-hand dense-grid approximation. Both sides are right continuous, so equality on a fixed dense sequence implies equality at every nonnegative time.
-- source:
--   Kyprianou (2006), Chapter 2 Lemma 2.12; local absolutely summable cumulative series and right continuity

import Mathlib
open MeasureTheory Set Function Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.cadlagLinearResidualFromDenseGridV1
    (f : ℝ≥0 → ℝ) (d : ℝ)
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (hf : ∀ t : ℝ≥0, ContinuousWithinAt f (Ici t) t)
    (hs : ∀ T : ℝ≥0, Summable (fun s : Ioc (0 : ℝ≥0) T =>
      |f s - Function.leftLim f s|))
    (heq : ∀ k : ℕ, f (grid k) = d * (grid k : ℝ) +
      ∑' s : Ioc (0 : ℝ≥0) (grid k), (f s - Function.leftLim f s)) :
    ∀ T : ℝ≥0, f T = d * (T : ℝ) +
      ∑' s : Ioc (0 : ℝ≥0) T, (f s - Function.leftLim f s) := by
  sorry
