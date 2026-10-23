-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_separation_constant_budget
-- name    : OAI.PiExponent.FormalInterpolation.separation_constant_budget
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-22T21:45:10.44146+00:00
-- url     : https://prove2.me/theorems/89fe48a7-d457-4a76-ac98-63eefcc1ace2
-- title:
--   The separation constant fits the derivative cost budget
-- statement:
--   For positive sigma and m ≥ 1, the explicit interpolation separation constant is positive and large enough that m²/C ≤ sigma. This converts the quantitative child’s derivative cost bound into the target cutoff.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_AdmissibleDeterminantParameters

open OAI.PiExponent

theorem OAI.PiExponent.FormalInterpolation.separation_constant_budget (m : Nat) (sigma : Rat)
    (hm : 1 ≤ m) (hsigma : 0 < (sigma : Real)) :
    0 < interpolationSeparationConstant m sigma ∧
      (m : Real) ^ 2 / interpolationSeparationConstant m sigma ≤ (sigma : Real) := by sorry
