-- Prove2me | Theorems.Thm_MazurTransfer_order27_denominator_nonzero
-- name    : MazurTransfer.order27_denominator_nonzero
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:38:08.703879+00:00
-- url     : https://prove2.me/theorems/5dea108a-c312-495f-9d7a-c770602e7215
-- title:
--   The first order-27 construction denominator is nonzero
-- statement:
--   Write $T(f,\xi)=T_0(f,\xi)+T_1(f,\xi)+T_2(f,\xi)+T_3(f,\xi)$ and $D(f,\xi)=D_0(f,\xi)+D_1(f,\xi)$ for the fixed imported trisection and denominator chunks. For $f,\xi\in\mathbb Q$, if $f\ne0,1$ and $T(f,\xi)=0$, then $$D(f,\xi)\ne0.$$ This regularity result permits the downstream construction of the kernel-cubic coordinate. The original statement has exactly these hypotheses.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.DenominatorNonzero, tl_d_ne. Full signature extracted from Lean AST ranges. Original aggregation and regularity proofs retained; expensive primitive identities use exact public certificates.

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

theorem MazurTransfer.order27_denominator_nonzero {f ξ : ℚ} (hf0 : f ≠ 0) (hf1 : f ≠ 1)
    (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlD0 f ξ + tlD1 f ξ) ≠ 0  := by sorry
