-- Prove2me | Theorems.Thm_MasulloRH_theta_gaussian_truncation_error
-- name    : MasulloRH.theta_gaussian_truncation_error
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T15:23:04.811059+00:00
-- url     : https://prove2.me/theorems/2e9c99f7-cd06-43f7-a85b-f4d2cc422151
-- title:
--   An explicit finite Gaussian-series enclosure for the dyadic theta function
-- statement:
--   Define the three-scale Gaussian
--
--   $$\psi(t)=e^{-\pi t^2}-3e^{-4\pi t^2}+2e^{-16\pi t^2},$$
--
--   and the logarithmic theta function
--
--   $$\theta(x)=\sum_{k\in\mathbb Z}\psi(ke^x).$$
--
--   For $x\in\mathbb R$ and $K\in\mathbb N$, let
--
--   $$S_K(x)=2\sum_{k=1}^{K}\psi(ke^x),\qquad \alpha=\pi e^{2x}>0.$$
--
--   Then the finite symmetric truncation has the explicit error bound
--
--   $$
--   |\theta(x)-S_K(x)|
--   \le\frac{12e^{-\alpha(K+1)^2}}{1-e^{-\alpha(2K+3)}}.
--   $$
--
--   The denominator is strictly positive for every allowed $x,K$. The estimate includes $K=0$, when the finite sum is empty. It bounds the actual theta function used by the mission's Gaussian approximation definition and needs no Riemann-hypothesis, Mertens, or density assumption.
--
--   This is a pointwise truncation estimate useful for rigorous theta evaluation. Additional control of quadrature and integration tails is needed to turn it into enclosures for the mission's weighted Gram integrals; that stronger numerical-certification procedure is not asserted here.
--
--   **Formalization Note.** The theta function and the finite sum are complex-valued with real summands; the left side is their complex norm. The finite sum is indexed in Lean by $n=0,\ldots,K-1$, with Gaussian argument $(n+1)e^x$.
-- source:
--   Original elementary truncation estimate for the exact definition MasulloRH_GaussianThetaApproximation, https://prove2.me/definitions/6f34c003-4870-4c6a-b83e-256b289a15db . Supporting the rational theta Gram interval-table target https://prove2.me/theorems/7f59c68d-29e6-404c-a754-27288c412b6c . This is independent supporting formalization, not an estimate claimed to be extracted from Masullo's paper. The finite geometric-series domination is fully proved in the submitted solution.

import Definitions.Def_MasulloRH_GaussianThetaApproximation

set_option autoImplicit false
open scoped BigOperators
open MasulloRH.GaussianApproximation

theorem MasulloRH.theta_gaussian_truncation_error (x : ℝ) (K : ℕ) :
    ‖theta x - 2 * ∑ n ∈ Finset.range K,
      ((Real.exp (-Real.pi * (((n : ℝ) + 1) * Real.exp x) ^ 2) -
        3 * Real.exp (-Real.pi * (2 * (((n : ℝ) + 1) * Real.exp x)) ^ 2) +
        2 * Real.exp (-Real.pi * (4 * (((n : ℝ) + 1) * Real.exp x)) ^ 2) : ℝ) : ℂ)‖ ≤
      12 * Real.exp (-Real.pi * (Real.exp x) ^ 2 * ((K : ℝ) + 1) ^ 2) /
        (1 - Real.exp (-Real.pi * (Real.exp x) ^ 2 * (2 * (K : ℝ) + 3))) := by sorry
