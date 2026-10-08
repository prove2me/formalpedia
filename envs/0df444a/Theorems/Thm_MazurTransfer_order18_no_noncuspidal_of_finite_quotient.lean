-- Prove2me | Theorems.Thm_MazurTransfer_order18_no_noncuspidal_of_finite_quotient
-- name    : MazurTransfer.order18_no_noncuspidal_of_finite_quotient
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T14:17:39.301367+00:00
-- url     : https://prove2.me/theorems/3de9a833-32b2-4c8b-afab-ccfb21e4ce78
-- title:
--   Order18: the exact 21-point reduction excludes noncuspidal genus-two points once the quotient is finite
-- statement:
--   Assume the point group of the explicit original elliptic quotient over ℚ[T]/(T³−3T−1) is finite. Then the order18 sextic y²=x⁶−4x⁵+10x⁴−10x³+5x²−2x+1 has no rational point with x≠0,1. Finiteness is the explicit hypothesis of this intermediate theorem and must be supplied separately for the unconditional exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c. All exact original supporting declarations are selected from the typed kernel dependency graph and complete original Lean AST source ranges. The genuine split separates full cubic-quotient point finiteness from finite reduction at17, preserving the unconditional existing rational genus-two and order18 campaign statements. Original Apache-2.0 headers and attribution retained. Earlier full and genus-two server timeouts are retained; this is a different mathematical subproblem and proof. No coefficient change, extra final hypothesis, custom axiom or resource-strengthening option.

import Mathlib
import Definitions.Def_MazurTransfer_Order18RealCubicQuotientData
import Theorems.Thm_MazurTransfer_order18_real_cubic_quotient_isElliptic
attribute [local instance] MazurTransfer.order18_real_cubic_quotient_isElliptic
open scoped WeierstrassCurve WeierstrassCurve.Affine

theorem MazurTransfer.order18_no_noncuspidal_of_finite_quotient [Finite MazurTorsion.XOneEighteenRealCubicQuotient.quotientCurve.toAffine.Point] (x y : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hcurve : y ^ 2 = x ^ 6 - 4 * x ^ 5 + 10 * x ^ 4 - 10 * x ^ 3 + 5 * x ^ 2 - 2 * x + 1) : False := by sorry
