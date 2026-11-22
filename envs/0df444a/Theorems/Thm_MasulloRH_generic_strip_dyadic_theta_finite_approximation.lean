-- Prove2me | Theorems.Thm_MasulloRH_generic_strip_dyadic_theta_finite_approximation
-- name    : MasulloRH.generic_strip_dyadic_theta_finite_approximation
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T21:42:25.979086+00:00
-- url     : https://prove2.me/theorems/617da3b9-8345-4a27-9341-4395751abdf9
-- title:
--   Finite-translate synthesis from interior zeta-divisor moments in generic subcritical strips
-- statement:
--   For Lebesgue-almost every real strip width $b$ with $0<b<1/2$, the following holds simultaneously for all $p\ge0$. Put
--
--   $$w_{b,p}(x)=(1+|x|)^p e^{b|x|}.$$
--
--   Let $f:\mathbb R\to\mathbb C$ be measurable with $w_{b,p}|f|\in L^2(\mathbb R)$. Assume the actual registered divisor-moment condition: for every nontrivial zero $\rho$ of the Riemann zeta function with $|\Re\rho-1/2|<b$, and every integer $0\le r<\operatorname{ord}_\rho(\zeta)$,
--
--   $$\int_{\mathbb R} f(x)x^r e^{(\rho-1/2)x}\,dx=0.$$
--
--   Write $\Theta$ for the literal centered dyadic Gaussian theta seed `MasulloRH.rationalDyadicThetaSeed` in the registered GaussianThetaDivision definition. Then for every $\delta>0$ there are $m\in\mathbb N$, complex coefficients $a_0,\ldots,a_{m-1}$ and real shifts $y_0,\ldots,y_{m-1}$ such that the residual has finite weighted $L^2$ norm and
--
--   $$\int_{\mathbb R} \left(w_{b,p}(x)\left|f(x)-\sum_{i=0}^{m-1}a_i\Theta(x-y_i)\right|\right)^2dx<\delta.$$
--
--   The exceptional null set of widths is chosen before $p$, $f$, and $\delta$. The empty sum is allowed. The explicit residual MemLp conclusion ensures the real integral inequality is not using a default value for a nonintegrable function.
--
--   This is the forward finite-translate synthesis consequence of generic-strip division. It does not assert the reverse inclusion, the critical endpoint $b=1/2$, approximation of an arbitrary Gaussian pulse without the moment conditions, identification with the manuscript's full geometric quotient, a trace formula, or RH.
-- source:
--   Analytic corollary of MasulloRH.generic_strip_dyadic_theta_division (24df0c86-b075-4107-9103-8fc580dde151): https://prove2.me/theorems/24df0c86-b075-4107-9103-8fc580dde151 . Uses the exact GaussianThetaDivision Definition 2ac9f610-07e0-499f-a791-cff8f32571cb. The weighted Young and literal theta/quartic kernel facts are attributed extractions from marozols's accepted division proof 0ab415f7-6816-4b40-b9ec-50067de21560. New proof work supplies the dual-annihilator/Fubini finite-translate closure, strong weighted translation/approximate identity, and explicit finite-sum assembly. This is an independent analytic bridge for the rational-theta part of the Masullo mission, not a claim that the manuscript's global/local trace comparison has been established.

import Mathlib
import Definitions.Def_MasulloRH_GaussianThetaDivision

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped Topology Convolution

theorem MasulloRH.generic_strip_dyadic_theta_finite_approximation :
    ∀ᵐ b : ℝ, 0 < b → b < 1/2 → ∀ p : ℝ, 0 ≤ p → ∀ f : ℝ → ℂ,
      Measurable f →
      MemLp (fun x : ℝ => ((1+|x|)^p * Real.exp (b*|x|)) * ‖f x‖) 2 volume →
      _root_.MasulloRH.RationalStripDivisorMoments b f → ∀ δ : ℝ, 0 < δ →
      ∃ (m : ℕ) (a : Fin m → ℂ) (y : Fin m → ℝ),
        MemLp (fun x : ℝ => ((1+|x|)^p * Real.exp (b*|x|)) *
          ‖f x - ∑ i : Fin m, a i * _root_.MasulloRH.rationalDyadicThetaSeed (x-y i)‖)
          2 volume ∧
        (∫ x : ℝ, (((1+|x|)^p * Real.exp (b*|x|)) *
          ‖f x - ∑ i : Fin m, a i * _root_.MasulloRH.rationalDyadicThetaSeed (x-y i)‖)^2) < δ := by sorry
