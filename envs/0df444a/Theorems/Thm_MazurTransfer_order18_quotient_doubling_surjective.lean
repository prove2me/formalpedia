-- Prove2me | Theorems.Thm_MazurTransfer_order18_quotient_doubling_surjective
-- name    : MazurTransfer.order18_quotient_doubling_surjective
-- status  : Open
-- author  : @Vas
-- created : 2026-10-07T14:38:29.218098+00:00
-- url     : https://prove2.me/theorems/06c090d4-6d54-47e5-a9f0-18c86ba705a7
-- title:
--   Order18: doubling is surjective on the exact cubic quotient point group
-- statement:
--   Let \(K=\mathbb{Q}[T]/(T^3-3T-1)\) and let \(E/K\) be the original explicit elliptic quotient. Every point of \(E(K)\) is twice a point of \(E(K)\): \[\forall P\in E(K),\quad\exists Q\in E(K),\quad 2Q=P.\] There is no rank, descent, finiteness or local-solubility hypothesis. This is the arithmetic input to the separately checked point-group finiteness consumer.
-- source:
--   Original WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c with exact cubic-field and quotient coefficients preserved. This is a genuine arithmetic boundary for the original full point-finiteness target. The preceding 17857-line server timeout remains retained. Finite generation comes from the original checked naive-height descent (Michael Stoll source, Apache-2.0); the rank calculation follows XOneEighteenFinalRankZero. No extra hypothesis is added to the final genus-two or campaign statement.

import Mathlib
import Definitions.Def_MazurTransfer_Order18RealCubicQuotientData
import Theorems.Thm_MazurTransfer_order18_real_cubic_quotient_isElliptic
attribute [local instance] MazurTransfer.order18_real_cubic_quotient_isElliptic
open scoped WeierstrassCurve WeierstrassCurve.Affine

theorem MazurTransfer.order18_quotient_doubling_surjective : Function.Surjective (nsmulAddMonoidHom (α := MazurTorsion.XOneEighteenRealCubicQuotient.quotientCurve.toAffine.Point) 2) := by sorry
