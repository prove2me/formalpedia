-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_interpolationSeparationConstant_dominates_factorial_factor
-- name    : OAI.PiExponent.FormalInterpolation.interpolationSeparationConstant_dominates_factorial_factor
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:08:58.728435+00:00
-- url     : https://prove2.me/theorems/c42caeb8-373f-4870-ba35-9d243a881f94
-- title:
--   Separation constant dominates the factorial coefficient
-- statement:
--   For positive sigma and k ≤ m + 1, the factorial coefficient in the geometric bound is bounded by the defined separation constant. From its definition, use k! ≤ (m + 2)^k, then bound each power using k ≤ m + 1 and positivity of sigma. This removes the numerical comparison from the parent proof, including the k = 0 boundary case.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.interpolationSeparationConstant_dominates_factorial_factor
    (m k : Nat) (hk : k ≤ m + 1) (sigma : Rat)
    (hsigma : 0 < (sigma : Real)) :
    2 * (k.factorial : Real) *
        (((m : Real) + 2) / (sigma : Real)) ^ k ≤
      interpolationSeparationConstant m sigma := by sorry
