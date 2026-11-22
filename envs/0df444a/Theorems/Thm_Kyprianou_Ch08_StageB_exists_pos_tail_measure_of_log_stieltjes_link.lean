-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_exists_pos_tail_measure_of_log_stieltjes_link
-- name    : Kyprianou.Ch08.StageB.exists_pos_tail_measure_of_log_stieltjes_link
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T19:04:35.149205+00:00
-- url     : https://prove2.me/theorems/3cbb60c4-2429-4237-af99-fbc0a332580f
-- title:
--   Positive-height closed-tail measure from a log-line Stieltjes link (public)
-- statement:
--   From a positive-height tail G with one-sided regularity (antitone on positives, right-continuous, vanishing at infinity) and a left-limit link identifying a closed-tail function F, there is a Borel measure on the reals with exact closed-tail values mu([h,∞)) = ofReal(F h) and finite closed tails for every positive h. The construction pushes a log-line Stieltjes measure forward along the exponential, avoiding global real-valued hypotheses at zero.
-- source:
--   Public decomposition child of Kyprianou Chapter 8 Theorem 8.2 actual-height proof (parent 3eded364-8075-43f9-bae4-12db613bec33): isolates the provable Stieltjes measure-construction step with explicit regularity hypotheses, separating it from the probabilistic tail-regularity and multiplicative-law gaps that remain with the parent. Public version enabling import by the public parent; the private helper 0d2e67bf is not importable by public targets.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

theorem Kyprianou.Ch08.StageB.exists_pos_tail_measure_of_log_stieltjes_link
    (G F : ℝ → ℝ)
    (G_anti : AntitoneOn G (Set.Ioi 0))
    (G_cont : ∀ h₀ : ℝ, 0 < h₀ → ContinuousWithinAt G (Set.Ici h₀) h₀)
    (G_top : Tendsto G atTop (nhds 0))
    (hlink : ∀ y : ℝ, 0 < y → Tendsto (fun s => -G s) (nhdsWithin y (Set.Iio y)) (nhds (-F y))) :
    ∃ mu : Measure ℝ, (∀ h : ℝ, 0 < h → mu (Set.Ici h) = ENNReal.ofReal (F h)) ∧
      (∀ h : ℝ, 0 < h → mu (Set.Ici h) < ⊤) := by
  sorry
