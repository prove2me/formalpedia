-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_unit_sheaf_cech_h1_finrank
-- name    : MazurTransfer.order13_actual_unit_sheaf_cech_h1_finrank
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T22:28:34.645844+00:00
-- url     : https://prove2.me/theorems/b68db36f-d3ed-4eb8-bb08-8e7af824c65a
-- title:
--   Actual order-13 curve: unit-sheaf Cech H1 has dimension two
-- statement:
--   Let $K$ be any field. Form the explicit curve $C$ by gluing $y^2=x^6+2x^5+x^4+2x^3+6x^2+4x+1$ to its reciprocal chart using $z=x^{-1}$, $w=yx^{-3}$. Let $U_0$ and $U_1$ be the images of these two specified affine charts. They form a two-affine-open cover, and the genuine unit sheaf of modules on $C$ has Cech cokernel of dimension two for this cover:
--
--   $$\dim_K\operatorname{coker}\bigl(\Gamma(U_0,\mathcal O_C)\oplus\Gamma(U_1,\mathcal O_C)\longrightarrow\Gamma(U_0\cap U_1,\mathcal O_C)\bigr)=2.$$
--
--   The boundary is restriction from the second chart minus restriction from the first. This supplies the exact two-chart sheaf interface used by the FLT genus comparison. The result holds over every field; no smoothness, derived-cohomology comparison, or function-field genus conclusion is part of this statement.
-- source:
--   Original complete affine and projective curve construction by Vasily Ilin: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/AlgebraicGeometry ; XOneThirteenAffineCurve.lean and XOneThirteenProjectiveCurve.lean, all mathematical declarations preserved; only import headers combined. Apache-2.0. Two-affine-open-cover and sectionsOf interfaces from https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions , Def_AlgebraicGeometry_TwoAffineOpenCover.lean and Def_AlgebraicGeometry_TwoChartCechSectionsOf.lean. New section-map comparison and dimension calculation by Vas and contributors.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
open AlgebraicGeometry

theorem MazurTransfer.order13_actual_unit_sheaf_cech_h1_finrank (K : Type*) [Field K] :
    ∃ W : (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).TwoAffineOpenCover,
      W.U0 = (MazurTorsion.XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange ∧
      W.U1 = (MazurTorsion.XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange ∧
      Module.finrank K (W.sectionsOf
        (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)
        (SheafOfModules.unit
          (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).ringCatSheaf)).H1 = 2 := by sorry
