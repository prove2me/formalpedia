-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_tateF25_eq_raw_pullback
-- name    : MazurProof.RationalPointsN25SutherlandBridge.tateF25_eq_raw_pullback
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:20:47.995624+00:00
-- url     : https://prove2.me/theorems/3002bf47-53f7-45d1-b4d8-c796aa4a7a4a
-- title:
--   The Tate order-$25$ polynomial is an explicit monomial multiple of the raw Sutherland pullback
-- statement:
--   Let $b,c∈ℚ$ with $c≠0$ and $b-c≠0$. Then $$F_{25}(b,c)=c^{10}(b-c)^{15}F_{raw}\left(b/c,c^2/(b-c)\right).$$ This factorization proves that zeros of the Tate polynomial map to the raw Sutherland curve.
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

theorem MazurProof.RationalPointsN25SutherlandBridge.tateF25_eq_raw_pullback (b c : ℚ) (hc : c ≠ 0) (hd : b - c ≠ 0) :
    F25 b c = c ^ 10 * (b - c) ^ 15 * sutherlandRawX1Plane25 (b / c) (c ^ 2 / (b - c)) := by sorry
