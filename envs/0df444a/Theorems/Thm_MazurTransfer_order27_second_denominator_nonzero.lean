-- Prove2me | Theorems.Thm_MazurTransfer_order27_second_denominator_nonzero
-- name    : MazurTransfer.order27_second_denominator_nonzero
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:38:00.777985+00:00
-- url     : https://prove2.me/theorems/82e00641-e16a-4a54-a179-d3e6595721bc
-- title:
--   The second order-27 construction denominator is nonzero
-- statement:
--   Let $M(f,Z)$ be the fixed imported kernel cubic, and let $E(f,Z)$ be the fixed second denominator polynomial. For $f,Z\in\mathbb Q$, if $M(f,Z)=0$, $f\ne0,1$ and $f^3-6f^2+3f+1\ne0$, then $$E(f,Z)\ne0.$$ This regularity result permits dividing by $E(f,Z)^2$ to construct the third rational hauptmodul leg. All four displayed hypotheses are retained in the exact interface.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion.Kubert.OrderTwentySevenLegStagesD.Bezout, zl_e_ne. Full signature extracted from Lean AST ranges. Original aggregation and regularity proofs retained; expensive primitive identities use exact public certificates.

import Mathlib
import Definitions.Def_MazurTransfer_OrderTwentySevenLegs
import Definitions.Def_MazurTransfer_OrderTwentySevenTrisectionData
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData4
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5

open MazurTorsion.Kubert

theorem MazurTransfer.order27_second_denominator_nonzero {f Z : ℚ} (hM : kernelCubicM f Z = 0) (hf0 : f ≠ 0)
    (hf1 : f ≠ 1) (hK : f ^ 3 - 6 * f ^ 2 + 3 * f + 1 ≠ 0) :
    zlE0 f Z ≠ 0  := by sorry
