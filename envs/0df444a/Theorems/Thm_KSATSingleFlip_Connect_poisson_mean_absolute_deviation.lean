-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_poisson_mean_absolute_deviation
-- name    : KSATSingleFlip.Connect.poisson_mean_absolute_deviation
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:40:13.834551+00:00
-- url     : https://prove2.me/theorems/0f714544-3f8d-42d7-b175-234879036718
-- title:
--   Mean absolute deviation of a Poisson clause count
-- statement:
--   If N has a Poisson distribution with mean r ≥ 0, then its mean absolute deviation from r is at most √r. This is the mean-fluctuation estimate used in the proof of the Poisson-count part of Lemma 2.6.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 2.6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem KSATSingleFlip.Connect.poisson_mean_absolute_deviation (r : ℝ≥0) :
    (∫ k : ℕ, |(k:ℝ) - (r:ℝ)| ∂(poissonMeasure r)) ≤ Real.sqrt (r:ℝ) := by sorry
