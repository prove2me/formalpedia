-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_sutherlandRawToOptimized_bihomogeneous_identity
-- name    : MazurProof.RationalPointsN25SutherlandBridge.sutherlandRawToOptimized_bihomogeneous_identity
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:21:32.005497+00:00
-- url     : https://prove2.me/theorems/3765ea79-7623-4818-bb96-d7f72520c995
-- title:
--   The optimized Sutherland equation pulls back to the raw equation with an explicit factor
-- statement:
--   Let $r,s∈ℚ$. Write $F_{raw}(r,s)$ for the raw affine equation of $X_1(25)$ and $F_{opt}^{bh}(X,K,A,B)$ for the bihomogenized optimized equation. Under the substitution $X=s-r$, $K=rs-2r+1$, $A=1$, and $B=s^2-s-r+1$, one has $$F_{opt}^{bh}(s-r,rs-2r+1,1,s^2-s-r+1)=(r-s)^4(s-1)^3(rs-2r+1)^2F_{raw}(r,s).$$ This is the polynomial identity connecting the Tate-normal-form source equation to the optimized projective model.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_RationalPointsN25SutherlandBridge
import Definitions.Def_TateOrder25Factor

open MazurProof
open MazurProof.RationalPointsN25SutherlandBridge
open MazurProof.TateOrder25Factor
set_option linter.style.longLine false

theorem MazurProof.RationalPointsN25SutherlandBridge.sutherlandRawToOptimized_bihomogeneous_identity (r s : ℚ) :
    sutherlandBihomogenized25
        (s - r) (r * s - 2 * r + 1) 1 (s ^ 2 - s - r + 1) =
      (r - s) ^ 4 * (s - 1) ^ 3 * (r * s - 2 * r + 1) ^ 2 *
        sutherlandRawX1Plane25 r s := by sorry
