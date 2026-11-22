-- Prove2me | Theorems.Thm_MasulloRH_theta_reflection
-- name    : MasulloRH.theta_reflection
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T15:48:32.57518+00:00
-- url     : https://prove2.me/theorems/8632ce84-3f47-4ac8-b2ff-ae87b3a5a9fe
-- title:
--   Exact Poisson reflection of the dyadic Gaussian theta function
-- statement:
--   Let
--
--   $$\psi(t)=e^{-\pi t^2}-3e^{-4\pi t^2}+2e^{-16\pi t^2},\qquad\theta(x)=\sum_{k\in\mathbb Z}\psi(ke^x).$$
--
--   Then, for every $x\in\mathbb R$,
--
--   $$\theta(x)=\frac{e^{-x}}{2}\,\theta(-x-\log4).$$
--
--   The affine reflection fixes $x=-\log2$. The identity makes evaluation at large negative arguments possible through evaluation at large positive arguments, where the Gaussian series converges rapidly. It also converts explicit right-hand decay estimates into left-hand estimates useful for weighted Gram-integral tails.
--
--   **Formalization Note.** This is the exact theta function in the published GaussianThetaApproximation definition. Its complex-valued series has real summands. The equality has no RH, Mertens, density, or integrability hypothesis.
-- source:
--   Elementary consequence of Gaussian Poisson summation, formalized for the exact dyadic coefficients (1,-3,2) in MasulloRH_GaussianThetaApproximation, https://prove2.me/definitions/6f34c003-4870-4c6a-b83e-256b289a15db . The proof applies Mathlib Real.tsum_exp_neg_mul_int_sq at the positive scales exp(x), 2*exp(x), and 4*exp(x), proves all needed summability, and rearranges the resulting three terms. This is independent supporting formalization for the Masullo RH mission, not an identity claimed to be newly discovered or extracted from a particular page of Masullo's draft.

import Definitions.Def_MasulloRH_GaussianThetaApproximation
open MasulloRH.GaussianApproximation
set_option autoImplicit false

theorem MasulloRH.theta_reflection (x : ℝ) :
    theta x = ((Real.exp (-x) / 2 : ℝ) : ℂ) * theta (-x - Real.log 4) := by sorry
