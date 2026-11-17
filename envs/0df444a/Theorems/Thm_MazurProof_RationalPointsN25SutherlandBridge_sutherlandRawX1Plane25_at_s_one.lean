-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_sutherlandRawX1Plane25_at_s_one
-- name    : MazurProof.RationalPointsN25SutherlandBridge.sutherlandRawX1Plane25_at_s_one
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:21:23.867054+00:00
-- url     : https://prove2.me/theorems/1ea698e1-9bdd-42d6-b8f2-566921ab6231
-- title:
--   The raw Sutherland equation at $s=1$ is $(r-1)^{10}$
-- statement:
--   For every $r∈ℚ$, the raw Sutherland polynomial specializes to $$F_{raw}(r,1)=(r-1)^{10}.$$ This specialization rules out $s=1$ away from the base point $r=1$.
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

theorem MazurProof.RationalPointsN25SutherlandBridge.sutherlandRawX1Plane25_at_s_one (r : ℚ) : sutherlandRawX1Plane25 r 1 = (r - 1) ^ 10 := by sorry
