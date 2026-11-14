-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_poisson_zero_count_deterministic
-- name    : KSATSingleFlip.Connect.poisson_zero_count_deterministic
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:00:07.726086+00:00
-- url     : https://prove2.me/theorems/0975b2c6-a084-462e-b6a7-8f9ebd6242d4
-- title:
--   Zero Poisson count gives a deterministic observable
-- statement:
--   If the count has Poisson mean zero, and the observable is constant on the zero-count event, then its probability of falling any positive amount below its mean is zero. This supplies the zero-mean case in Lemma 2.6.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 2.6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem KSATSingleFlip.Connect.poisson_zero_count_deterministic {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Ω → ℕ) (hN : Measurable N) (hNlaw : Measure.map N P = poissonMeasure 0)
    (Y : Ω → ℝ) (c u : ℝ) (hu : 0 < u) (hzero : ∀ ω, N ω = 0 → Y ω = c) :
    P.real {ω | Y ω ≤ (∫ ω, Y ω ∂P)-u} = 0 := by sorry
