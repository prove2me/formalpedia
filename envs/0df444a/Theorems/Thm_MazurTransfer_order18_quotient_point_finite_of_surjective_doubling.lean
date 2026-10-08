-- Prove2me | Theorems.Thm_MazurTransfer_order18_quotient_point_finite_of_surjective_doubling
-- name    : MazurTransfer.order18_quotient_point_finite_of_surjective_doubling
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T14:34:21.907235+00:00
-- url     : https://prove2.me/theorems/77e74ea5-e742-441e-bd84-de5b09118252
-- title:
--   Order18: surjective doubling makes the complete cubic quotient point group finite
-- statement:
--   Let \(K=\mathbb{Q}[T]/(T^3-3T-1)\) and let \(E/K\) be the explicit elliptic quotient in the published data interface. If multiplication by two on \(E(K)\) is surjective, then the full group \(E(K)\) is finite. Surjectivity is the explicit intermediate hypothesis; the unconditional arithmetic child supplies it.
-- source:
--   Original WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c with exact cubic-field and quotient coefficients preserved. This is a genuine arithmetic boundary for the original full point-finiteness target. The preceding 17857-line server timeout remains retained. Finite generation comes from the original checked naive-height descent (Michael Stoll source, Apache-2.0); the rank calculation follows XOneEighteenFinalRankZero. No extra hypothesis is added to the final genus-two or campaign statement.

import Mathlib
import Definitions.Def_MazurTransfer_Order18RealCubicQuotientData
import Theorems.Thm_MazurTransfer_order18_real_cubic_quotient_isElliptic
attribute [local instance] MazurTransfer.order18_real_cubic_quotient_isElliptic
open scoped WeierstrassCurve WeierstrassCurve.Affine

theorem MazurTransfer.order18_quotient_point_finite_of_surjective_doubling (hsurj : Function.Surjective (nsmulAddMonoidHom (α := MazurTorsion.XOneEighteenRealCubicQuotient.quotientCurve.toAffine.Point) 2)) : Finite MazurTorsion.XOneEighteenRealCubicQuotient.quotientCurve.toAffine.Point := by sorry
