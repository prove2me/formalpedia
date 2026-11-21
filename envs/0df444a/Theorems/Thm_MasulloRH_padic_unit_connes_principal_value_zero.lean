-- Prove2me | Theorems.Thm_MasulloRH_padic_unit_connes_principal_value_zero
-- name    : MasulloRH.padic_unit_connes_principal_value_zero
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:37:08.427821+00:00
-- url     : https://prove2.me/theorems/6e3bce00-472b-4584-a129-b0f6a51786df
-- title:
--   Vanishing of the p-adic Connes principal value on the unit indicator
-- statement:
--   Let $p$ be a rational prime, and normalize additive Haar measure $dx$ on $\mathbb Q_p$ by $\operatorname{vol}(\mathbb Z_p)=1$. Let $\psi\colon\mathbb Q_p\to\mathbb T$ be a continuous additive character with kernel $\mathbb Z_p$. For $u(x)=\mathbf 1_{\mathbb Z_p^\times}(1+x)$ write
--   $$\widehat u(y)=\int_{\mathbb Q_p}u(x)\,\psi(xy)\,dx.$$
--   Then $y\mapsto\log|y|_p\,\widehat u(y)$ is integrable and its integral vanishes. In the local normalization of Appendix B.4.4, this is the vanishing of the Connes–Weil principal value on the unit indicator. Up to a scalar, this is the finite-place test for a radial idelic function supported at norms in $(1/2,2)$.
-- source:
--   Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, Examples A.3.1.6–7, Definition B.4.4.1, Lemma B.4.4.5, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. See also Alain Connes, Trace Formula in Noncommutative Geometry and the Zeros of the Riemann Zeta Function, Appendix II, Lemma 2, https://arxiv.org/abs/math/9811068.

import Mathlib

open MeasureTheory Set Metric

theorem MasulloRH.padic_unit_connes_principal_value_zero
    {p : ℕ} [Fact p.Prime] [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]
    (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure]
    (ψ : AddChar ℚ_[p] Circle) (hcont : Continuous ψ)
    (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1)
    (hμ : μ (closedBall (0 : ℚ_[p]) 1) = 1) :
    let f : ℚ_[p] → ℂ := fun y ↦ (Real.log ‖y‖ : ℂ) *
      (∫ x in {x : ℚ_[p] | ‖1 + x‖ = 1}, (ψ (x * y) : ℂ) ∂μ)
    Integrable f μ ∧ (∫ y, f y ∂μ) = 0 := by sorry
