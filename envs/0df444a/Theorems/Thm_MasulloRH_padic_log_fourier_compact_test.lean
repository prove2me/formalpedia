-- Prove2me | Theorems.Thm_MasulloRH_padic_log_fourier_compact_test
-- name    : MasulloRH.padic_log_fourier_compact_test
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T04:02:15.649294+00:00
-- url     : https://prove2.me/theorems/5306aad8-aa51-45db-806b-01c3531d0fad
-- title:
--   Exact logarithmic Fourier distribution on rational p-adic compact tests
-- statement:
--   Let $p$ be prime, normalize additive Haar measure by $\mu(\mathbb Z_p)=1$, and let $\psi$ be a continuous additive character of $\mathbb Q_p$ with kernel $\mathbb Z_p$. For every compactly supported locally constant complex test $f$, set
--   $$
--   \widehat f(y)=\int_{\mathbb Q_p} f(x)\psi(xy)\,d\mu(x),\qquad
--   g(x)=f(x)-f(0)\mathbf1_{\mathbb Z_p}(x).
--   $$
--   Both logarithmic and subtracted-kernel pairings are absolutely convergent, with
--   $$
--   \int_{\mathbb Q_p}\log|y|_p\,\widehat f(y)\,d\mu(y)
--   =-\frac{\log p}{1-p^{-1}}\int_{\mathbb Q_p}\frac{g(x)}{|x|_p}\,d\mu(x)
--   -\frac{\log p}{p-1}f(0).
--   $$
--   This gives the whole additive logarithmic distribution in the rational finite-place normalization. Dividing by $\log p$ gives the distribution for $J_v$ as defined in (B.4.3.2).
-- source:
--   Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, Proposition B.4.3.1, Eqs. (B.4.3.2)–(B.4.3.5), https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. Uses the verified ball formula 9552b2e0 and Haar scaling helpers adapted from lll, Prove2Me submission 41fd4c8f-fb18-4544-94b6-3abef11cea1b (Apache-2.0).

import Mathlib

open MeasureTheory
open scoped Topology

theorem MasulloRH.padic_log_fourier_compact_test {p : ℕ} [Fact p.Prime] [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]
    (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure]
    (ψ : AddChar ℚ_[p] Circle) (hcont : Continuous ψ)
    (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1)
    (hμ : μ (Metric.closedBall (0 : ℚ_[p]) 1) = 1)
    (f : ℚ_[p] → ℂ) (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) :
    let g := fun x : ℚ_[p] ↦ f x-f 0*(Metric.closedBall (0 : ℚ_[p]) 1).indicator (fun _ ↦ (1:ℂ)) x
    let F := fun y : ℚ_[p] ↦ (Real.log ‖y‖ : ℂ) * ∫ x, f x * (ψ (x*y) : ℂ) ∂μ
    Integrable F μ ∧ Integrable (fun x : ℚ_[p] ↦ g x/(‖x‖:ℂ)) μ ∧
      (∫ y, F y ∂μ) =
        -(Real.log p/(1-(p : ℝ)⁻¹) : ℝ) * (∫ x, g x/(‖x‖:ℂ) ∂μ) -
        ((Real.log p/((p:ℝ)-1) : ℝ) : ℂ) * f 0 := by sorry
