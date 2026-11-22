-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanBrownianPhiHarmonicRoot
-- name    : Kyprianou.Ch01.mckeanBrownianPhiHarmonicRoot
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T15:43:55.137801+00:00
-- url     : https://prove2.me/theorems/131c59f6-e334-443a-8887-66b28e65e58a
-- title:
--   McKean Brownian passage exponent solves discounted generator characteristic equation
-- statement:
--   The positive exponential exponent in McKean perpetual American put is the positive root of the Brownian discounted-generator equation (sigma squared divided by two) phi squared minus drift gamma times phi minus discount q equals zero. This supplies the q-harmonicity algebra on the continuation region for the stopped value supermartingale verification.
-- source:
--   Kyprianou (2006), Chapter 1 Theorem 1.13; drifted Brownian generator and exponential characteristic equation.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanBrownianPhiHarmonicRoot
    (sigma gamma q : ℝ) (hsigma : 0 < sigma) (hq : 0 < q) :
    let phi : ℝ :=
      (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) /
        sigma ^ 2
    (sigma ^ 2 / 2) * phi ^ 2 - gamma * phi - q = 0 := by sorry
