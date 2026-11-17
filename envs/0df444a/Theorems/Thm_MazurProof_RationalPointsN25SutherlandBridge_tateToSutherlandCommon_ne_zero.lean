-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_tateToSutherlandCommon_ne_zero
-- name    : MazurProof.RationalPointsN25SutherlandBridge.tateToSutherlandCommon_ne_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:19:54.838443+00:00
-- url     : https://prove2.me/theorems/09606561-f6ec-4ac8-9c87-1809b638d009
-- title:
--   The common Tate-to-Sutherland denominator is nonzero on the order-$25$ locus
-- statement:
--   Let $b,c∈ℚ$ satisfy $F_{25}(b,c)=0$, $c≠0$, and $b-c≠0$. Then the explicit common factor obeys $$C_{25}(b,c)≠0.$$ This makes the optimized Sutherland $X$-coordinate well defined.
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

theorem MazurProof.RationalPointsN25SutherlandBridge.tateToSutherlandCommon_ne_zero {b c : ℚ} (hF : F25 b c = 0)
    (hc : c ≠ 0) (hd : b - c ≠ 0) : tateToSutherlandCommon25 b c ≠ 0 := by sorry
