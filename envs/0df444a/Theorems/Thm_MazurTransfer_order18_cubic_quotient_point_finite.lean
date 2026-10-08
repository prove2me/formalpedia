-- Prove2me | Theorems.Thm_MazurTransfer_order18_cubic_quotient_point_finite
-- name    : MazurTransfer.order18_cubic_quotient_point_finite
-- status  : Open
-- author  : @Vas
-- created : 2026-10-07T14:19:16.96413+00:00
-- url     : https://prove2.me/theorems/65c90d27-54dc-4238-86a0-2c955d0242ff
-- title:
--   Order18: all points of the exact real-cubic quotient form a finite group
-- statement:
--   The rational point group over the exact cubic coefficient field of the original elliptic quotient is finite. There is no rank, descent or finiteness hypothesis in this statement.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c. All exact original supporting declarations are selected from the typed kernel dependency graph and complete original Lean AST source ranges. The genuine split separates full cubic-quotient point finiteness from finite reduction at17, preserving the unconditional existing rational genus-two and order18 campaign statements. Original Apache-2.0 headers and attribution retained. Earlier full and genus-two server timeouts are retained; this is a different mathematical subproblem and proof. No coefficient change, extra final hypothesis, custom axiom or resource-strengthening option.

import Mathlib
import Definitions.Def_MazurTransfer_Order18RealCubicQuotientData
import Theorems.Thm_MazurTransfer_order18_real_cubic_quotient_isElliptic
attribute [local instance] MazurTransfer.order18_real_cubic_quotient_isElliptic
open scoped WeierstrassCurve WeierstrassCurve.Affine

theorem MazurTransfer.order18_cubic_quotient_point_finite : Finite MazurTorsion.XOneEighteenRealCubicQuotient.quotientCurve.toAffine.Point := by sorry
