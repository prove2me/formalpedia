-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_picard_representation_charZero
-- name    : MazurTransfer.order13_actual_picard_representation_charZero
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-09T09:45:59.502799+00:00
-- url     : https://prove2.me/theorems/74b8254b-5b74-40b1-babf-cd99b04aba0e
-- title:
--   Actual Picard representation of the order-13 curve over every characteristic-zero field
-- statement:
--   Let $K$ be any characteristic-zero field, and let $C/K$ be the unchanged two-chart curve
--   $$y^2=x^6+2x^5+x^4+2x^3+6x^2+4x+1$$
--   with reciprocal gluing $z=x^{-1}$ and $w=yx^{-3}$. The curve has a $K$-rational section. For every such section $\varepsilon$, there exists a scheme $P/K$ representing the full rigidified relative Picard subfunctor of line bundles algebraically equivalent to zero, with its specified universal rigidified line bundle. Moreover, $P/K$ is smooth, proper and geometrically connected.
--
--   The statement applies over $K=\mathbb Q$ without assuming algebraic closedness, supplying a Picard scheme or imposing a rational-point hypothesis. It establishes the actual rational Picard representation needed for the subsequent Abel-Jacobi construction and rational-point obstruction.
-- source:
--   Actual curve: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/AlgebraicGeometry . Exact finite-etale chart, Picard representation, affine-open containment and descent contracts: https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems . Sources include Thm_AlgebraicGeometry_RelPicard_exists_finite_etale_hasChartSections_of_field.lean, Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_algEquivZeroCut_of_finiteMapData_of_isReduced.lean, Thm_AlgebraicGeometry_RelPicard_exists_isAffineOpen_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData.lean, and Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_of_finite_etale_descent_of_finiteMapData.lean. Actual characteristic-zero specializations and literal (0,1) section by Vas and contributors; Apache-2.0 attribution retained.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicGeometry_LocalRepresentabilityULift
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_JacJ1Iface
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

theorem MazurTransfer.order13_actual_picard_representation_charZero.{u} (K : Type u) [Field K] [CharZero K] :
    Nonempty (SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)) ∧
    ∀ ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K),
      ∃ D : RelativePic0Designation K (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K),
        Nonempty (RepresentsRelSubPic
          (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) ε
          (algEquivZeroCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) ε) D) ∧
        Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase := by sorry
