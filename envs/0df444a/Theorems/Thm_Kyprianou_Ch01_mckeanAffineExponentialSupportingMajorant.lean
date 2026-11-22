-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanAffineExponentialSupportingMajorant
-- name    : Kyprianou.Ch01.mckeanAffineExponentialSupportingMajorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T20:35:51.67249+00:00
-- url     : https://prove2.me/theorems/4d510e79-4c2d-4b01-a6cd-852c5278a781
-- title:
--   Global positive-intercept affine-exponential supporting majorant for McKean value
-- statement:
--   A novel elementary path to McKean verification avoiding stochastic Ito–Tanaka. Let b=log(K phi/(1+phi)), u=min(y,b), A=K-(1+1/phi)exp(u), B=exp(u)/phi. Then A,B≥0 and the original piecewise McKean candidate V touches the exponential-affine support A+B exp(-phi(z-u)) at z=y, and lies below it for all z. The lower branch follows from exp(h)≥1+h and exp(-phi h)≥1-phi h, yielding phi exp(h)+exp(-phi h)≥phi+1. For z≥b, use the majorant at b and convex interpolation with exp(-phi(z-b))∈(0,1], using A≥0. When y≥b, A=0 and the support coincides with the continuation branch. This global supporting majorant is the key elementary alternative to the difficult Ito/local-time formula and is sufficient for Brownian semigroup q-excessivity by integrating the proved negative-root exponential martingale.
-- source:
--   Kyprianou (2006) Ch 1 Theorem 1.13, convex-analytic support for McKean q-excessivity.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanAffineExponentialSupportingMajorant
    (K phi y : ℝ) (hK : 0 < K) (hphi : 0 < phi) :
    let b : ℝ := Real.log (K * phi / (1 + phi))
    let u : ℝ := min y b
    let A : ℝ := K - (1 + 1 / phi) * Real.exp u
    let B : ℝ := Real.exp u / phi
    0 ≤ A ∧ 0 ≤ B ∧
      mckeanValue K b phi y =
        A + B * Real.exp (-phi * (y - u)) ∧
      ∀ z : ℝ, mckeanValue K b phi z ≤
        A + B * Real.exp (-phi * (z - u)) := by sorry
