-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25SutherlandBridge_tateToSutherlandY_eq_raw
-- name    : MazurProof.RationalPointsN25SutherlandBridge.tateToSutherlandY_eq_raw
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:20:07.166129+00:00
-- url     : https://prove2.me/theorems/98ae6829-c3ac-4dea-b41c-b00e327665f5
-- title:
--   The optimized Sutherland $Y$-coordinate equals the cleared raw-coordinate formula
-- statement:
--   Let $b,c∈ℚ$ with $c≠0$, $b-c≠0$, and nonzero transformed $Y$-denominator. Put $r=b/c$ and $s=c^2/(b-c)$. Then $$\frac{rs-2r+1}{s^2-s-r+1}=\frac{C_{25}(b,c)(b-c)}{D_{25}(b,c)},$$ where $C_{25}$ is the common factor and $D_{25}$ is the explicit $Y$-denominator. This identifies the raw and optimized Sutherland coordinates.
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

theorem MazurProof.RationalPointsN25SutherlandBridge.tateToSutherlandY_eq_raw
    {b c : ℚ} (hc : c ≠ 0) (hd : b - c ≠ 0)
    (hB : tateToSutherlandYDen25 b c ≠ 0) :
    ((b / c) * (c ^ 2 / (b - c)) - 2 * (b / c) + 1) /
        ((c ^ 2 / (b - c)) ^ 2 - c ^ 2 / (b - c) - b / c + 1) =
      tateToSutherlandCommon25 b c * (b - c) /
        tateToSutherlandYDen25 b c := by sorry
