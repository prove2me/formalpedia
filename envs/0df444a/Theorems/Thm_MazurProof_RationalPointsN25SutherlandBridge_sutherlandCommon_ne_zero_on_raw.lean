-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_sutherlandCommon_ne_zero_on_raw
-- name    : MazurProof.RationalPointsN25SutherlandBridge.sutherlandCommon_ne_zero_on_raw
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:20:33.57835+00:00
-- url     : https://prove2.me/theorems/f9e325e0-712f-42dd-8113-dc134a45d96b
-- title:
--   The common raw-to-optimized factor is nonzero away from $r=1$
-- statement:
--   Let $r,s∈ℚ$ satisfy the raw Sutherland equation and assume $r≠1$. Then $$rs-2r+1≠0.$$ This proves that the common denominator in the optimized coordinate transformation does not vanish on the relevant raw locus.
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

theorem MazurProof.RationalPointsN25SutherlandBridge.sutherlandCommon_ne_zero_on_raw {r s : ℚ} (hraw : sutherlandRawX1Plane25 r s = 0) (hr1 : r ≠ 1) :
    r * s - 2 * r + 1 ≠ 0 := by sorry
