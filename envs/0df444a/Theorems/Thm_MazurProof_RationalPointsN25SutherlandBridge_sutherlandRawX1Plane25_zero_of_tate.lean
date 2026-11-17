-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_sutherlandRawX1Plane25_zero_of_tate
-- name    : MazurProof.RationalPointsN25SutherlandBridge.sutherlandRawX1Plane25_zero_of_tate
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:21:14.978198+00:00
-- url     : https://prove2.me/theorems/17ab0c07-d72a-44a9-b5f3-01ed574fd931
-- title:
--   The Tate order-$25$ equation pulls back to the raw Sutherland equation
-- statement:
--   Let $b,c∈ℚ$ satisfy $F_{25}(b,c)=0$, $c≠0$, and $b-c≠0$. Then with $r=b/c$ and $s=c^2/(b-c)$, $$F_{raw}(r,s)=0.$$ This is the first algebraic step from Tate normal form to the Sutherland model.
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

theorem MazurProof.RationalPointsN25SutherlandBridge.sutherlandRawX1Plane25_zero_of_tate {b c : ℚ} (hF : F25 b c = 0)
    (hc : c ≠ 0) (hd : b - c ≠ 0) : sutherlandRawX1Plane25 (b / c) (c ^ 2 / (b - c)) = 0 := by sorry
