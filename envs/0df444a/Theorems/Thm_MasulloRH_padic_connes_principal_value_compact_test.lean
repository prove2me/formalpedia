-- Prove2me | Theorems.Thm_MasulloRH_padic_connes_principal_value_compact_test
-- name    : MasulloRH.padic_connes_principal_value_compact_test
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T04:07:43.248595+00:00
-- url     : https://prove2.me/theorems/e333104d-e6a5-47b8-9052-9e041bd2109e
-- title:
--   Connes–Weil principal value for every rational p-adic compact test
-- statement:
--   Let $p$ be a rational prime, normalize additive Haar measure by $\mu(\mathbb Z_p)=1$, and let $\psi$ be a continuous additive character with kernel $\mathbb Z_p$. For a compactly supported locally constant test $f$ with $f(0)=0$, set $u(x)=f(1+x)/|1+x|_p^{1/2}$. This is the additive test in (B.4.4.7). Both sides of the following identity are absolutely convergent:
--   $$
--   -\int_{\mathbb Q_p}\log|y|_p\,\widehat u(y)\,d\mu(y)
--   =\frac{\log p}{1-p^{-1}}
--   \int_{\mathbb Q_p}
--   \frac{f(x)-f(1)\mathbf1_{\mathbb Z_p^\times}(x)}
--   {|x|_p^{1/2}|x-1|_p}\,d\mu(x).
--   $$
--   Here $\widehat u(y)=\int u(x)\psi(xy)\,d\mu(x)$. This is (B.4.4.14) for $\mathbb Q_p$ written in additive coordinates. For the multiplicative Haar measure with unit mass on $\mathbb Z_p^\times$, the density is $d^\times x=d\mu(x)/((1-p^{-1})|x|_p)$, which accounts for the square-root weight.
-- source:
--   Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, Lemma B.4.4.5, Eqs. (B.4.4.7) and (B.4.4.14), https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. Uses the verified additive compact-test distribution 5306aad8 and shifted-unit cancellation 6e3bce00.

import Mathlib

open MeasureTheory
open scoped Topology

theorem MasulloRH.padic_connes_principal_value_compact_test {p : ℕ} [Fact p.Prime] [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]
    (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure]
    (ψ : AddChar ℚ_[p] Circle) (hcont : Continuous ψ)
    (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1)
    (hμ : μ (Metric.closedBall (0 : ℚ_[p]) 1) = 1)
    (f : ℚ_[p] → ℂ) (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) (hf0 : f 0 = 0) :
    let F := fun y : ℚ_[p] ↦ (Real.log ‖y‖ : ℂ) *
      ∫ x : ℚ_[p], (f (1+x)/(Real.sqrt ‖1+x‖:ℂ)) * (ψ (x*y):ℂ) ∂μ
    let K := fun x : ℚ_[p] ↦
      ((f x-f 1*{x : ℚ_[p] | ‖x‖ = 1}.indicator (fun _ ↦ (1:ℂ)) x)/(Real.sqrt ‖x‖:ℂ))/(‖x-1‖:ℂ)
    Integrable F μ ∧ Integrable K μ ∧
      -(∫ y, F y ∂μ) = ((Real.log p/(1-(p:ℝ)⁻¹) : ℝ) : ℂ)*(∫ x, K x ∂μ) := by sorry
