-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanAffineCoefficientsNonnegative
-- name    : Kyprianou.Ch01.mckeanAffineCoefficientsNonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T20:53:17.762953+00:00
-- url     : https://prove2.me/theorems/9bc69a5c-277e-483d-bf1b-e5b966f5be14
-- title:
--   Affine McKean support coefficients are nonnegative at the clipped exercise state
-- statement:
--   The source barrier has exp(b)=K phi/(1+phi). For u=min(y,b)≤b this gives exp(u)≤exp(b). Multiply by the nonnegative factor (1+1/phi) and simplify (1+1/phi)exp(b)=K to obtain the nonnegative affine intercept. B=exp(u)/phi is positive. This is a short necessary sublemma for the global McKean affine supporting majorant attached to Chapter 1.
-- source:
--   Kyprianou (2006), Chapter 1, McKean exercise barrier algebra.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanAffineCoefficientsNonnegative
    (K phi y : ℝ) (hK : 0 < K) (hphi : 0 < phi) :
    let b := Real.log (K * phi / (1 + phi))
    let u := min y b
    0 ≤ K - (1 + 1 / phi) * Real.exp u ∧
      0 ≤ Real.exp u / phi := by sorry
