-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_place_cech_h1_finrank
-- name    : MazurTransfer.order13_actual_place_cech_h1_finrank
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T23:33:01.159812+00:00
-- url     : https://prove2.me/theorems/47477f58-e7da-419d-94dc-e5f668ef68e3
-- title:
--   Dimension two for the actual order-13 valuation-place Cech cohomology
-- statement:
--   Let $K$ be a field of characteristic zero, and let $C$ be the curve obtained by gluing $y^2=x^6+2x^5+x^4+2x^3+6x^2+4x+1$ to its reciprocal chart by $z=x^{-1}$ and $w=yx^{-3}$. The curve is integral. Write $F=K(C)$ for its actual function field and $U_0,U_1$ for the two chart images in $C$.
--
--   For $i=0,1$, let $S_i$ be the discrete valuation places of $F/K$ centered at closed points of $U_i$. For a set $S$ of such places, put $L(S)=\{f\in F:v(f)\geq 0\text{ for every }v\in S\}$. Then
--
--   $$\dim_K\frac{L(S_0\cap S_1)}{L(S_0)+L(S_1)}=2.$$
--
--   This is the valuation-place Čech cohomology of the specified chart cover of the specified curve. It supplies the concrete dimension needed by the function-field cohomology and Riemann–Roch comparison. The statement does not yet identify this quotient with the global repartition cohomology defining function-field genus.
-- source:
--   Original explicit sextic and chart gluing: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/AlgebraicGeometry . Complete genuine valuation/place definitions and complete scheme/place section-comparison proof: https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 , Definitions/Def_AlgebraicCurve_PlacesOf.lean, Definitions/Def_AlgebraicCurve_CechSectionsOfDivisor.lean, P2M/Sol/S_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1.lean. Actual section quotient computation and application bridge by Vas and contributors, Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
open AlgebraicGeometry CategoryTheory

theorem MazurTransfer.order13_actual_place_cech_h1_finrank.{u} (K : Type u) [Field K] [CharZero K] :
    ∃ (hC : IsIntegral (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K)),
      letI := hC
      letI := (AlgebraicCurve.baseToFunctionField
        (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)).toAlgebra
      ∃ (W : (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).TwoAffineOpenCover),
        W.U0 = (MazurTorsion.XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange ∧
        W.U1 = (MazurTorsion.XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange ∧
        Module.finrank K (AlgebraicCurve.cechH1
          (AlgebraicCurve.placesOf (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) W.U0)
          (AlgebraicCurve.placesOf (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) W.U1)
          (0 : AlgebraicCurve.Divisor K
            (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).functionField)) = 2 := by sorry
