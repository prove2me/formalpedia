-- Prove2me | Theorems.Thm_MasulloRH_padic_radial_shell_log_fourier
-- name    : MasulloRH.padic_radial_shell_log_fourier
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T03:20:25.321418+00:00
-- url     : https://prove2.me/theorems/2b11e831-5225-4ec2-8e4b-6557aa16a7c1
-- title:
--   Logarithmic additive Fourier pairing of a rational p-adic valuation shell
-- statement:
--   Let $p$ be a rational prime. Normalize additive Haar measure on $\mathbb Q_p$ by $\mu(\mathbb Z_p)=1$ and let $\psi$ be a continuous additive character with kernel $\mathbb Z_p$. For each integer $k$, let $f_k$ be the indicator of the translated valuation shell $\{x:|x+1|_p=p^k\}$. Define its additive transform by $\widehat f_k(y)=\int f_k(x)\psi(xy)\,d\mu(x)$.
--
--   The product of the transform and the logarithm of the norm is integrable, and its integral is
--   $$
--   \int_{\mathbb Q_p}\log|y|_p\,\widehat f_k(y)\,d\mu(y)
--   =\begin{cases}
--   0,& k=0,\\
--   -\log(p)\min(p^k,1),& k\ne0.
--   \end{cases}
--   $$
--   This gives the rational finite-place logarithmic pairing separately on every radial shell. The sign is that of the logarithmic Fourier distribution. The principal value in (B.4.4.1) includes its prescribed minus sign.
-- source:
--   Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, Proposition B.4.3.1 and Definition B.4.4.1, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. Compare A. Connes, Trace Formula in Noncommutative Geometry and the Zeros of the Riemann Zeta Function, Appendix II, https://arxiv.org/pdf/math/9811068#page=72. Haar scaling helpers adapted from lll, Prove2Me submission 41fd4c8f-fb18-4544-94b6-3abef11cea1b (Apache-2.0).

import Mathlib

open MeasureTheory
open scoped Topology

theorem MasulloRH.padic_radial_shell_log_fourier {p : ℕ} [Fact p.Prime] [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]
    (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure]
    (ψ : AddChar ℚ_[p] Circle)
    (hcont : Continuous ψ) (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1)
    (hμ : μ (Metric.closedBall (0 : ℚ_[p]) 1) = 1) (k : ℤ) :
    let F := fun y : ℚ_[p] ↦ (Real.log ‖y‖ : ℂ) *
      (∫ x in Metric.sphere (0 : ℚ_[p]) ((p : ℝ)^k), (ψ ((x-1)*y) : ℂ) ∂μ)
    Integrable F μ ∧ (∫ y, F y ∂μ) =
      if k = 0 then 0 else -(Real.log p : ℂ) * ((min ((p : ℝ)^k) 1 : ℝ) : ℂ) := by sorry
