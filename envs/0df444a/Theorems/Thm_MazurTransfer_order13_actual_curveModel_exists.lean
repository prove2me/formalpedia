-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_curveModel_exists
-- name    : MazurTransfer.order13_actual_curveModel_exists
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T23:03:29.834983+00:00
-- url     : https://prove2.me/theorems/7d3f614a-2eec-4b02-b064-b0558de206da
-- title:
--   Genuine curve model for the actual order-13 sextic
-- statement:
--   Let $K$ be a field of characteristic zero. Glue the ordinary chart $y^2=x^6+2x^5+x^4+2x^3+6x^2+4x+1$ and its reciprocal chart by $z=x^{-1}$ and $w=yx^{-3}$, obtaining the specified curve $C$ with structure map $c:C\to\operatorname{Spec}K$.
--
--   There exist a field $F$ with a $K$-algebra structure, a genuine curve model $M$ of $F/K$, and an isomorphism $e:M.C\xrightarrow{\sim} C$ over $K$:
--
--   $$c\circ e=M.\mathrm{toBase}.$$
--
--   Here a curve model includes an integral smooth proper curve of relative dimension one, an identification with its function field over $K$, a bijection between closed points and the discrete valuation places trivial on $K$, the exact equality between stalk images and valuation rings, and an affine open containing every given finite subset of points. The model is constructed on the specified curve itself with its actual function field. This result provides the model required by the FLT sheaf-cohomology/genus comparison; it does not yet assert the genus or exclude any rational torsion order.
-- source:
--   Original explicit affine and reciprocal gluing by Vasily Ilin, retained whole: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/AlgebraicGeometry , XOneThirteenAffineCurve.lean, XOneThirteenProjectiveCurve.lean, XOneThirteenHyperellipticMap.lean. Genuine CurveModel definition and complete supporting stalk/valuation proofs: https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 , Definitions/Def_AlgebraicCurve_CurveModel.lean, P2M/Sol/S_AlgebraicCurve_exists_place_range_stalk_eq.lean, S_AlgebraicCurve_eq_of_range_stalk_eq.lean, S_AlgebraicCurve_exists_closedPoint_range_stalk_eq.lean. New projective-line moving affine opens and actual model assembly by Vas and contributors, Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicCurve_CurveModel
open AlgebraicGeometry CategoryTheory

theorem MazurTransfer.order13_actual_curveModel_exists.{u} (K : Type u) [Field K] [CharZero K] :
    ∃ (F : Type u) (_ : Field F) (_ : Algebra K F)
      (M : AlgebraicCurve.CurveModel K F)
      (e : M.C ≅ MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K),
      e.hom ≫ MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K = M.toBase := by sorry
