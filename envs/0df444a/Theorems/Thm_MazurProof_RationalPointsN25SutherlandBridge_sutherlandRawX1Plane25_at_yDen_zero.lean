-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_sutherlandRawX1Plane25_at_yDen_zero
-- name    : MazurProof.RationalPointsN25SutherlandBridge.sutherlandRawX1Plane25_at_yDen_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:19:57.000016+00:00
-- url     : https://prove2.me/theorems/d11e3fb9-f780-4289-bbb5-3a8f13582661
-- title:
--   On the vanishing $Y$-denominator locus, the raw Sutherland polynomial is explicit
-- statement:
--   For every $s∈ℚ$, substituting $r=s^2-s+1$ gives $$F_{raw}(s^2-s+1,s)=-s(s-1)^{27}.$$ This shows that the optimized $Y$-denominator can vanish on the raw curve only at the excluded values $s=0$ or $s=1$.
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

theorem MazurProof.RationalPointsN25SutherlandBridge.sutherlandRawX1Plane25_at_yDen_zero (s : ℚ) :
    sutherlandRawX1Plane25 (s ^ 2 - s + 1) s = -(s * (s - 1) ^ 27) := by sorry
