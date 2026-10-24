-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_power_from_nonzero_scalar_mem
-- name    : OAI.PiExponent.FormalInterpolation.coordinate_power_from_nonzero_scalar_mem
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:55:57.144902+00:00
-- url     : https://prove2.me/theorems/5f938727-a3b5-4e95-9772-8b58dc87b68d
-- title:
--   Remove a nonzero scalar from coordinate-power ideal membership
-- statement:
--   A nonzero complex scalar is a unit, so its factor can be removed from ideal membership. If `n > 0`, use that exponent; if `n = 0`, the ideal contains one and hence contains `X i` with exponent one.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

theorem OAI.PiExponent.FormalInterpolation.coordinate_power_from_nonzero_scalar_mem
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) ℂ)) (i : Fin d)
    (n : Nat) (c : ℂ) (hc : c ≠ 0)
    (h : MvPolynomial.C c * (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n ∈ I) :
    ∃ N : Nat, 0 < N ∧
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ N ∈ I := by sorry
