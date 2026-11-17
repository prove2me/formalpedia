-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_tateToSutherlandYDen_ne_zero
-- name    : MazurProof.RationalPointsN25SutherlandBridge.tateToSutherlandYDen_ne_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:20:00.198489+00:00
-- url     : https://prove2.me/theorems/5c216f96-c215-42fc-9e6b-1c53e302b4c5
-- title:
--   The Tate-to-Sutherland $Y$-denominator is nonzero on the order-$25$ locus
-- statement:
--   Let $b,c∈ℚ$ satisfy $F_{25}(b,c)=0$, $c≠0$, and $b-c≠0$. Then the explicit denominator satisfies $$D_{25}(b,c)≠0.$$ This makes the optimized Sutherland $Y$-coordinate well defined.
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

theorem MazurProof.RationalPointsN25SutherlandBridge.tateToSutherlandYDen_ne_zero {b c : ℚ} (hF : F25 b c = 0)
    (hc : c ≠ 0) (hd : b - c ≠ 0) : tateToSutherlandYDen25 b c ≠ 0 := by sorry
