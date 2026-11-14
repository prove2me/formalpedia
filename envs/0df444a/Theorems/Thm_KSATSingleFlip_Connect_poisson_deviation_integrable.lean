-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_poisson_deviation_integrable
-- name    : KSATSingleFlip.Connect.poisson_deviation_integrable
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:43:00.425425+00:00
-- url     : https://prove2.me/theorems/c317e8c9-3622-48f2-8865-b71eccce6afa
-- title:
--   Integrability and mean absolute deviation of a Poisson count
-- statement:
--   For a Poisson count of mean r ≥ 0, the absolute deviation from r is integrable and its expectation is at most √r. This supplies the integrability needed to compare fixed-count and Poisson-count means in Lemma 2.6.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 2.6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem KSATSingleFlip.Connect.poisson_deviation_integrable (r : ℝ≥0) :
    Integrable (fun k : ℕ => |(k:ℝ) - (r:ℝ)|) (poissonMeasure r) ∧
    (∫ k : ℕ, |(k:ℝ) - (r:ℝ)| ∂(poissonMeasure r)) ≤ Real.sqrt (r:ℝ) := by sorry
