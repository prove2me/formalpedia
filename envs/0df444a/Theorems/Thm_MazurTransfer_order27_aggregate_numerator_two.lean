-- Prove2me | Theorems.Thm_MazurTransfer_order27_aggregate_numerator_two
-- name    : MazurTransfer.order27_aggregate_numerator_two
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T15:08:19.323973+00:00
-- url     : https://prove2.me/theorems/16ac2f4a-55bb-48d6-828d-b332f04fa24d
-- title:
--   Order-27 kernel-cubic numerator: two
-- statement:
--   Let $f,\xi\in\mathbb Q$ satisfy the fixed trisection equation $T(f,\xi)=0$. The displayed term of the kernel-cubic numerator equals the displayed complete sum of fixed polynomial remainder blocks. This is the full original tl_mnum₂ identity, with its original hypotheses and coefficient functions. The downstream consumer combines the four numerator terms and their zero sum to obtain $M(f,N(f,\xi)/D(f,\xi))=0$ when $D(f,\xi)\ne0$. No rational-point existence or torsion exclusion is assumed.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Full signatures extracted using Lean signature AST ranges; proof commands retained by kernel dependencies and resolved references. This is an exact split of the terminal timed-out kernel coordinate verification, preserving the original hypotheses and conclusion. Original Apache-2.0 file headers retained.

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData4
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5

open MazurTorsion.Kubert

theorem MazurTransfer.order27_aggregate_numerator_two :
(∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
-(3 * f * (f - 1) ^ 2 * (f ^ 2 + f - 1)) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) ^ 2
      * (tlD0 f ξ + tlD1 f ξ) =
      ((((((tlWTwoXP0c0 f ξ + tlWTwoXP0c1 f ξ) + (tlWTwoXP0c2 f ξ + tlWTwoXP0c3 f ξ)) +
        ((tlWTwoXP0c4 f ξ + tlWTwoXP0c5 f ξ) + (tlWTwoXP0c6 f ξ + tlWTwoXP0c7 f ξ))) +
        (((tlWTwoXP0c8 f ξ + tlWTwoXP0c9 f ξ) + (tlWTwoXP0c10 f ξ + tlWTwoXP0c11 f ξ)) +
        ((tlWTwoXP0c12 f ξ + tlWTwoXP0c13 f ξ) + (tlWTwoXP0c14 f ξ + tlWTwoXP0c15 f ξ)))) +
        ((((tlWTwoXP0c16 f ξ + tlWTwoXP0c17 f ξ) + (tlWTwoXP0c18 f ξ + tlWTwoXP0c19 f ξ)) +
        ((tlWTwoXP0c20 f ξ + tlWTwoXP1c0 f ξ) + (tlWTwoXP1c1 f ξ + tlWTwoXP1c2 f ξ))) +
        (((tlWTwoXP1c3 f ξ + tlWTwoXP1c4 f ξ) + (tlWTwoXP1c5 f ξ + tlWTwoXP1c6 f ξ)) +
        ((tlWTwoXP1c7 f ξ + tlWTwoXP1c8 f ξ) + (tlWTwoXP1c9 f ξ + tlWTwoXP1c10 f ξ))))) +
        (((((tlWTwoXP1c11 f ξ + tlWTwoXP1c12 f ξ) + (tlWTwoXP1c13 f ξ + tlWTwoXP1c14 f ξ)) +
        ((tlWTwoXP1c15 f ξ + tlWTwoXP1c16 f ξ) + (tlWTwoXP1c17 f ξ + tlWTwoXP1c18 f ξ))) +
        (((tlWTwoXP1c19 f ξ + tlWTwoXP1c20 f ξ) + (tlWTwoXP1c21 f ξ + tlWTwoXP2c0 f ξ)) +
        ((tlWTwoXP2c1 f ξ + tlWTwoXP2c2 f ξ) + (tlWTwoXP2c3 f ξ + tlWTwoXP2c4 f ξ)))) +
        ((((tlWTwoXP2c5 f ξ + tlWTwoXP2c6 f ξ) + (tlWTwoXP2c7 f ξ + tlWTwoXP2c8 f ξ)) +
        ((tlWTwoXP2c9 f ξ + tlWTwoXP2c10 f ξ) + (tlWTwoXP2c11 f ξ + tlWTwoXP2c12 f ξ))) +
        (((tlWTwoXP2c13 f ξ + tlWTwoXP2c14 f ξ) + (tlWTwoXP2c15 f ξ + tlWTwoXP2c16 f ξ)) +
        ((tlWTwoXP2c17 f ξ + tlWTwoXP2c18 f ξ) + (tlWTwoXP2c19 f ξ + tlWTwoXP2c20 f ξ)))))) +
        (((((tlWTwoXP2c21 f ξ + tlWTwoXP2c22 f ξ) + (tlWTwoXP3c0 f ξ + tlWTwoXP3c1 f ξ)) +
        ((tlWTwoXP3c2 f ξ + tlWTwoXP3c3 f ξ) + (tlWTwoXP3c4 f ξ + tlWTwoXP3c5 f ξ))) +
        (((tlWTwoXP3c6 f ξ + tlWTwoXP3c7 f ξ) + (tlWTwoXP3c8 f ξ + tlWTwoXP3c9 f ξ)) +
        ((tlWTwoXP3c10 f ξ + tlWTwoXP3c11 f ξ) + (tlWTwoXP3c12 f ξ + tlWTwoXP3c13 f ξ)))) +
        ((((tlWTwoXP3c14 f ξ + tlWTwoXP3c15 f ξ) + (tlWTwoXP3c16 f ξ + tlWTwoXP3c17 f ξ)) +
        ((tlWTwoXP3c18 f ξ + tlWTwoXP3c19 f ξ) + (tlWTwoXP3c20 f ξ + tlWTwoXP3c21 f ξ))) +
        (((tlWTwoXP4c0 f ξ + tlWTwoXP4c1 f ξ) + (tlWTwoXP4c2 f ξ + tlWTwoXP4c3 f ξ)) +
        ((tlWTwoXP4c4 f ξ + tlWTwoXP4c5 f ξ) + tlWTwoXP4c6 f ξ))))) := by sorry
