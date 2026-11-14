-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_poisson_fixed_count_mean
-- name    : KSATSingleFlip.Connect.poisson_fixed_count_mean
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:48:39.338514+00:00
-- url     : https://prove2.me/theorems/0941df43-f5b2-429a-8bbc-8a1e4a666222
-- title:
--   Fixed-count and Poisson-count mean comparison
-- statement:
--   If g is integrable under Poisson(r) and its value changes by at most L between consecutive counts, then |g(j)−E g(N)| ≤ L(|j−r|+√r) for every j. This is the exact comparison used for g(j)=E[F] at fixed clause count in the proof of Lemma 2.6.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 2.6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem KSATSingleFlip.Connect.poisson_fixed_count_mean (r : ℝ≥0) (g : ℕ → ℝ) (hg : Integrable g (poissonMeasure r))
    (L : ℝ) (hL : 0 ≤ L) (hstep : ∀ j, |g (j+1)-g j| ≤ L) (j : ℕ) :
    |g j - ∫ k, g k ∂(poissonMeasure r)| ≤ L*(|(j:ℝ)-(r:ℝ)|+Real.sqrt (r:ℝ)) := by sorry
