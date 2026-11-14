-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_2_6_poisson_from_fibers
-- name    : KSATSingleFlip.Connect.lemma_2_6_poisson_from_fibers
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:52:05.625237+00:00
-- url     : https://prove2.me/theorems/4daeaefa-9a79-43b4-8067-79531cffa950
-- title:
--   Lemma 2.6 Poisson bound from fixed-count fiber estimates
-- statement:
--   Suppose the count is Poisson with positive mean νn, g(j) is an integrable sequence of fixed-count means with adjacent differences bounded by L, the zero-count outcome equals g(0), and on each positive-count fiber the stated fixed-count lower-tail bound holds. If √(νn) ≤ an/(4L), then the lower tail below the Poisson mixture mean by an is at most 3 exp(−a²n/(128(ν+1)L²)). The fixed-count fiber hypothesis and identification of the mixture mean with the observable expectation remain to be established for the marked-clause model.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 2.6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Mathlib
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem KSATSingleFlip.Connect.lemma_2_6_poisson_from_fibers {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (hN : Measurable N) (F : Ω → ℝ) (hF : Measurable F)
    (r : ℝ≥0) (hr : 0 < r) (hNlaw : Measure.map N μ = poissonMeasure r)
    (ν a L n : ℝ) (hν : 0 ≤ ν) (ha : 0 < a) (ha1 : a ≤ 1)
    (hL : 1 ≤ L) (hn : 0 < n) (hrν : (r:ℝ) = ν*n)
    (hsqrt : Real.sqrt (ν*n) ≤ a*n/(4*L))
    (g : ℕ → ℝ) (hg : Integrable g (poissonMeasure r))
    (hstep : ∀ j, |g (j+1)-g j| ≤ L)
    (hzero : ∀ ω, N ω = 0 → F ω = g 0)
    (hfiber : ∀ j : ℕ, 1 ≤ j →
      μ ({ω | N ω = j} ∩ {ω | F ω ≤ g j - a*n/2}) ≤
        μ {ω | N ω = j} * ENNReal.ofReal (Real.exp (-(a*n)^2/(8*(j:ℝ)*L^2)))) :
    μ.real {ω | F ω ≤ (∫ k, g k ∂(poissonMeasure r)) - a*n} ≤
      3 * Real.exp (-(a^2*n)/(128*(ν+1)*L^2)) := by sorry
