-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_tateC_ne_zero_of_F25
-- name    : MazurProof.RationalPointsN25SutherlandBridge.tateC_ne_zero_of_F25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:20:06.070313+00:00
-- url     : https://prove2.me/theorems/a91841db-c021-444f-8c50-fed672ed9b15
-- title:
--   A nondegenerate Tate solution of the order-$25$ equation has $c≠0$
-- statement:
--   Let $b,c∈ℚ$. If $b≠0$ and the order-$25$ Tate polynomial satisfies $F_{25}(b,c)=0$, then $$c≠0.$$ This licenses the first rational substitution from Tate parameters to Sutherland coordinates.
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

theorem MazurProof.RationalPointsN25SutherlandBridge.tateC_ne_zero_of_F25 {b c : ℚ} (hb : b ≠ 0) (hF : F25 b c = 0) : c ≠ 0 := by sorry
