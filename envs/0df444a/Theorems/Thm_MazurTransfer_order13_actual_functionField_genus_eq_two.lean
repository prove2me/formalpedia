-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_functionField_genus_eq_two
-- name    : MazurTransfer.order13_actual_functionField_genus_eq_two
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-08T00:31:14.9005+00:00
-- url     : https://prove2.me/theorems/7229db40-e3a8-4edd-a14b-71d4547a9f8f
-- title:
--   Genuine function-field genus two for the actual order-13 curve
-- statement:
--   Let $K$ be a field of characteristic zero. Let $C$ be the specified curve obtained by gluing the affine chart
--
--   $$y^2=x^6+2x^5+x^4+2x^3+6x^2+4x+1$$
--
--   to its reciprocal chart using $z=x^{-1}$ and $w=yx^{-3}$. The curve is integral. Equip its actual function field $F=K(C)$, defined as the generic stalk of $C$, with its structural $K$-algebra map. Then its genuine function-field genus is two:
--
--   $$g(F/K)=\dim_K H^1_{\mathrm{rep}}(0)=2.$$
--
--   Here $H^1_{\mathrm{rep}}(0)$ is the global repartition quotient in the original FLT definitions, over all discrete valuation places of $F/K$. The curve structure, constant-field equality, finite-dimensional constant-function space and Riemann–Roch existence are proved from the actual curve. The literal affine point $(0,1)$ supplies a genuine degree-one valuation place, proving that the field of constants is exactly $K$. Algebraic closedness, an abstract genus datum and a Riemann–Roch witness are not additional assumptions. This establishes the geometric genus input for the Mazur order-13 program; the rational-point obstruction remains a separate theorem.
-- source:
--   Explicit sextic and gluing by Vasily Ilin, Apache-2.0: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/AlgebraicGeometry . Complete official FLT function-field, principal-divisor, Riemann–Roch and Cech/global comparison proofs, Apache-2.0: https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 . Sources include S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean, S_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver.lean, S_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one.lean, S_AlgebraicCurve_cechH1ToH1_bijective.lean and the original Repartitions/AdelicIndex definitions. Actual curve assembly, dimension computation and genus bridge by Vas and contributors. The characteristic-zero strengthening constructs the literal section (0,1), proves its center is a closed point, and applies the complete original S_AlgebraicCurve_Place_isRational_of_range_stalk_section_eq.lean proof.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_Repartitions
open AlgebraicGeometry CategoryTheory

theorem MazurTransfer.order13_actual_functionField_genus_eq_two.{u} (K : Type u) [Field K] [CharZero K] :
    ∃ (hC : IsIntegral (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K)),
      letI := hC
      letI := (AlgebraicCurve.baseToFunctionField
        (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)).toAlgebra
      AlgebraicCurve.genusFF K
        (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).functionField = 2 := by sorry
