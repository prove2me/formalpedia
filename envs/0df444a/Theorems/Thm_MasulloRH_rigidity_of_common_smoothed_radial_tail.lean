-- Prove2me | Theorems.Thm_MasulloRH_rigidity_of_common_smoothed_radial_tail
-- name    : MasulloRH.rigidity_of_common_smoothed_radial_tail
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T03:43:41.488213+00:00
-- url     : https://prove2.me/theorems/6d74e0a2-7271-4121-a614-c253fad1aacd
-- title:
--   Rigidity of a common limit for every sufficiently large radial tail under upper-cutoff smoothing
-- statement:
--   Let $F$ be a complex radial primitive and let the probability measures $\mu_n$ describing the upper endpoints eventually give full mass above each fixed radius. Suppose $F$ is integrable under each $\mu_n$. If for every $a\ge A$ the smoothed tail $\int(F(x)-F(a))\,d\mu_n(x)$ converges to a common value $C$, then $C=0$ and $F(a)=F(A)$ for all $a\ge A$. In particular this applies to upper-cutoff mixtures for the radial shell in (11.3.2.4) when the shell measure is independent of its lower threshold.
-- source:
--   Masullo, The Music of the Primes, printed p. 496, (11.3.2.4–5). F is the primitive of the fixed shell measure in this application.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
open Filter MeasureTheory
open scoped Topology

theorem MasulloRH.rigidity_of_common_smoothed_radial_tail (μ : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (μ n)]
    (F : ℝ → ℂ) (hF : ∀ n, Integrable F (μ n)) (A : ℝ) (C : ℂ)
    (hes : ∀ a : ℝ, ∀ᶠ n in atTop, ∀ᵐ x ∂μ n, a ≤ x)
    (hlim : ∀ a ≥ A, Tendsto (fun n => ∫ x, F x - F a ∂μ n) atTop (𝓝 C)) :
    C = 0 ∧ ∀ a ≥ A, F a = F A := by sorry
