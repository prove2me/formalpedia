-- Prove2me | Theorems.Thm_MasulloRH_padic_log_fourier_away_from_origin_ball
-- name    : MasulloRH.padic_log_fourier_away_from_origin_ball
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T03:50:43.180018+00:00
-- url     : https://prove2.me/theorems/9552b2e0-2eb8-4993-8124-92b5dac7e80d
-- title:
--   Logarithmic p-adic Fourier pairing on a ball avoiding the pole
-- statement:
--   Let $p$ be prime, let $\mu(\mathbb Z_p)=1$ for additive Haar measure on $\mathbb Q_p$, and let $\psi$ be a continuous additive character with kernel $\mathbb Z_p$. For $a\in\mathbb Q_p$ and $k\in\mathbb Z$ with $p^k<|a|_p$, write $B(a,p^k)=\{x:|x-a|_p\le p^k\}$. The logarithmic Fourier pairing of its indicator is absolutely convergent and satisfies
--   $$
--   \int_{\mathbb Q_p}\log|y|_p\left(\int_{B(a,p^k)}\psi(xy)\,d\mu(x)\right)d\mu(y)
--   =-\frac{\log p}{1-p^{-1}}\,\frac{p^k}{|a|_p}.
--   $$
--   On this ball $|x|_p=|a|_p$ and $\mu(B(a,p^k))=p^k$. Thus the value is the nonsingular integral of the kernel $-\log(p)/((1-p^{-1})|x|_p)$ on an arbitrary compact ball avoiding zero.
-- source:
--   Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, Proposition B.4.3.1 and Definition B.4.4.1, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. Compare A. Connes, Trace Formula in Noncommutative Geometry and the Zeros of the Riemann Zeta Function, Appendix II, https://arxiv.org/pdf/math/9811068#page=72. Haar scaling helpers adapted from lll, Prove2Me submission 41fd4c8f-fb18-4544-94b6-3abef11cea1b (Apache-2.0).

import Mathlib

open MeasureTheory
open scoped Topology

theorem MasulloRH.padic_log_fourier_away_from_origin_ball {p : ℕ} [Fact p.Prime] [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]
    (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure]
    (ψ : AddChar ℚ_[p] Circle) (hcont : Continuous ψ)
    (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1)
    (hμ : μ (Metric.closedBall (0 : ℚ_[p]) 1) = 1)
    (a : ℚ_[p]) (k : ℤ) (ha : (p : ℝ)^k < ‖a‖) :
    let F := fun y : ℚ_[p] ↦ (Real.log ‖y‖ : ℂ) *
      (∫ x in Metric.closedBall a ((p : ℝ)^k), (ψ (x*y) : ℂ) ∂μ)
    Integrable F μ ∧ (∫ y, F y ∂μ) =
      -(Real.log p/(1-(p : ℝ)⁻¹) : ℝ)*(((p : ℝ)^k/‖a‖ : ℝ) : ℂ) := by sorry
