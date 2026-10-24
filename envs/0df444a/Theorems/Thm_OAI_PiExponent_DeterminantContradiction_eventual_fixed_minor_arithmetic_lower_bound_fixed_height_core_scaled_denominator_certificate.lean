-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventual_fixed_minor_arithmetic_lower_bound_fixed_height_core_scaled_denominator_certificate
-- name    : OAI.PiExponent.DeterminantContradiction.eventual_fixed_minor_arithmetic_lower_bound_fixed_height_core_scaled_denominator_certificate
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-23T08:50:44.430985+00:00
-- url     : https://prove2.me/theorems/3cf1611f-6b0b-4306-9ca7-2ac1fe8446f0
-- title:
--   Scaled denominator certificate for a nonzero selected minor
-- statement:
--   At every positive height, a nonzero selected minor admits a positive integer scale making its determinant a nonzero Gaussian integer. The scale has the logarithmic upper bound controlled by the row-weight mean and arithmetic error.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.eventual_fixed_minor_arithmetic_lower_bound_fixed_height_core_scaled_denominator_certificate
    {nu : Real} (d : FixedData nu) (H : Real) (hH : 0 < H)
    (selection : Row d H → Column d H)
    (hdet : (actualMinor d H selection).det ≠ 0) :
    0 < (actualRowCount d H : Real) * H ∧
      ∃ D : Nat, 0 < D ∧
        ∃ a b : Int,
          (D : Complex) * (actualMinor d H selection).det =
              (a : Complex) + Complex.I * (b : Complex) ∧
            1 ≤ (D : Real) * ‖(actualMinor d H selection).det‖ ∧
            -(Real.log (D : Real)) ≤
              Real.log ‖(actualMinor d H selection).det‖ ∧
            Real.log (D : Real) ≤
              ((actualRowCount d H : Real) * H) *
                (1 - actualMean d H + d.arithmeticError) := by sorry
