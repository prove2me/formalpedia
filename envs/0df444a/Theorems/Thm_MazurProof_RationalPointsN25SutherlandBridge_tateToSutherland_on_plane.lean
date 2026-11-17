-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_tateToSutherland_on_plane
-- name    : MazurProof.RationalPointsN25SutherlandBridge.tateToSutherland_on_plane
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:19:50.316268+00:00
-- url     : https://prove2.me/theorems/72a526a7-0871-4d7a-9287-4f7bd17f5627
-- title:
--   Admissible order-$25$ Tate parameters map to the optimized Sutherland plane curve
-- statement:
--   Let $b,c∈ℚ$ satisfy $b≠0$, $F_5(b,c)≠0$, and $F_{25}(b,c)=0$. Define the transformed coordinates $$X=\frac{X_{num}(b,c)}{C_{25}(b,c)},\qquad Y=\frac{C_{25}(b,c)(b-c)}{D_{25}(b,c)}.$$ Then the optimized Sutherland equation satisfies $F_{Suth}(X,Y)=0$. This is the explicit source-model bridge from Tate normal form.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_RationalPointsN25SutherlandBridge
import Definitions.Def_TateNFDivision
import Definitions.Def_TateOrder25Factor

open MazurProof
open MazurProof.RationalPointsN25SutherlandBridge
open MazurProof.TateOrder25Factor
set_option linter.style.longLine false

theorem MazurProof.RationalPointsN25SutherlandBridge.tateToSutherland_on_plane
    {b c : ℚ} (hb : b ≠ 0) (h5 : TateNFDivision.F5 b c ≠ 0)
    (hF : F25 b c = 0) :
    sutherlandX1Plane25
        (tateToSutherlandXNum25 b c / tateToSutherlandCommon25 b c)
        (tateToSutherlandCommon25 b c * (b - c) /
          tateToSutherlandYDen25 b c) = 0 := by sorry
