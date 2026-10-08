-- Prove2me | Theorems.Thm_MazurTransfer_order27_aggregate_numerator_three
-- name    : MazurTransfer.order27_aggregate_numerator_three
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T15:08:30.281987+00:00
-- url     : https://prove2.me/theorems/ed1d75bc-2f41-4bf2-a1a3-01853419aa0c
-- title:
--   Order-27 kernel-cubic numerator: three
-- statement:
--   Let $f,\xi\in\mathbb Q$ satisfy the fixed trisection equation $T(f,\xi)=0$. The displayed term of the kernel-cubic numerator equals the displayed complete sum of fixed polynomial remainder blocks. This is the full original tl_mnum₃ identity, with its original hypotheses and coefficient functions. The downstream consumer combines the four numerator terms and their zero sum to obtain $M(f,N(f,\xi)/D(f,\xi))=0$ when $D(f,\xi)\ne0$. No rational-point existence or torsion exclusion is assumed.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Full signatures extracted using Lean signature AST ranges; proof commands retained by kernel dependencies and resolved references. This is an exact split of the terminal timed-out kernel coordinate verification, preserving the original hypotheses and conclusion. Original Apache-2.0 file headers retained.

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData4
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5

open MazurTorsion.Kubert

theorem MazurTransfer.order27_aggregate_numerator_three :
(∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
-(3 * f * (f - 1) * (3 * f ^ 9 - f ^ 8 - 26 * f ^ 7 + 94 * f ^ 6 - 168 * f ^ 5 + 187 * f ^ 4 -
      145 * f ^ 3 + 76 * f ^ 2 - 26 * f + 3)) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) *
      (tlD0 f ξ + tlD1 f ξ) ^ 2 =
      ((((((tlWOneXP0c0 f ξ + tlWOneXP0c1 f ξ) + (tlWOneXP0c2 f ξ + tlWOneXP0c3 f ξ)) +
        ((tlWOneXP0c4 f ξ + tlWOneXP0c5 f ξ) + (tlWOneXP0c6 f ξ + tlWOneXP0c7 f ξ))) +
        (((tlWOneXP0c8 f ξ + tlWOneXP0c9 f ξ) + (tlWOneXP0c10 f ξ + tlWOneXP0c11 f ξ)) +
        ((tlWOneXP0c12 f ξ + tlWOneXP0c13 f ξ) + (tlWOneXP0c14 f ξ + tlWOneXP1c0 f ξ)))) +
        ((((tlWOneXP1c1 f ξ + tlWOneXP1c2 f ξ) + (tlWOneXP1c3 f ξ + tlWOneXP1c4 f ξ)) +
        ((tlWOneXP1c5 f ξ + tlWOneXP1c6 f ξ) + (tlWOneXP1c7 f ξ + tlWOneXP1c8 f ξ))) +
        (((tlWOneXP1c9 f ξ + tlWOneXP1c10 f ξ) + (tlWOneXP1c11 f ξ + tlWOneXP1c12 f ξ)) +
        ((tlWOneXP1c13 f ξ + tlWOneXP1c14 f ξ) + (tlWOneXP1c15 f ξ + tlWOneXP1c16 f ξ))))) +
        (((((tlWOneXP2c0 f ξ + tlWOneXP2c1 f ξ) + (tlWOneXP2c2 f ξ + tlWOneXP2c3 f ξ)) +
        ((tlWOneXP2c4 f ξ + tlWOneXP2c5 f ξ) + (tlWOneXP2c6 f ξ + tlWOneXP2c7 f ξ))) +
        (((tlWOneXP2c8 f ξ + tlWOneXP2c9 f ξ) + (tlWOneXP2c10 f ξ + tlWOneXP2c11 f ξ)) +
        ((tlWOneXP2c12 f ξ + tlWOneXP2c13 f ξ) + (tlWOneXP2c14 f ξ + tlWOneXP2c15 f ξ)))) +
        ((((tlWOneXP2c16 f ξ + tlWOneXP2c17 f ξ) + (tlWOneXP2c18 f ξ + tlWOneXP3c0 f ξ)) +
        ((tlWOneXP3c1 f ξ + tlWOneXP3c2 f ξ) + (tlWOneXP3c3 f ξ + tlWOneXP3c4 f ξ))) +
        (((tlWOneXP3c5 f ξ + tlWOneXP3c6 f ξ) + (tlWOneXP3c7 f ξ + tlWOneXP3c8 f ξ)) +
        ((tlWOneXP3c9 f ξ + tlWOneXP3c10 f ξ) + (tlWOneXP3c11 f ξ + tlWOneXP3c12 f ξ)))))) +
        ((((((tlWOneXP3c13 f ξ + tlWOneXP3c14 f ξ) + (tlWOneXP3c15 f ξ + tlWOneXP3c16 f ξ)) +
        ((tlWOneXP3c17 f ξ + tlWOneXP3c18 f ξ) + (tlWOneXP3c19 f ξ + tlWOneXP4c0 f))) +
        (((tlWOneXP4c1 f ξ + tlWOneXP4c2 f ξ) + (tlWOneXP4c3 f ξ + tlWOneXP4c4 f ξ)) +
        ((tlWOneXP4c5 f ξ + tlWOneXP4c6 f ξ) + (tlWOneXP4c7 f ξ + tlWOneXP4c8 f ξ)))) +
        ((((tlWOneXP4c9 f ξ + tlWOneXP4c10 f ξ) + (tlWOneXP4c11 f ξ + tlWOneXP4c12 f ξ)) +
        ((tlWOneXP4c13 f ξ + tlWOneXP4c14 f ξ) + (tlWOneXP4c15 f ξ + tlWOneXP4c16 f ξ))) +
        (((tlWOneXP4c17 f ξ + tlWOneXP4c18 f ξ) + (tlWOneXP4c19 f ξ + tlWOneXP4c20 f ξ)) +
        ((tlWOneXP5c0 f ξ + tlWOneXP5c1 f ξ) + (tlWOneXP5c2 f ξ + tlWOneXP5c3 f ξ))))) +
        (((((tlWOneXP5c4 f ξ + tlWOneXP5c5 f ξ) + (tlWOneXP5c6 f ξ + tlWOneXP5c7 f ξ)) +
        ((tlWOneXP5c8 f ξ + tlWOneXP5c9 f ξ) + (tlWOneXP5c10 f ξ + tlWOneXP5c11 f ξ))) +
        (((tlWOneXP5c12 f ξ + tlWOneXP5c13 f ξ) + (tlWOneXP5c14 f ξ + tlWOneXP5c15 f ξ)) +
        ((tlWOneXP5c16 f ξ + tlWOneXP5c17 f ξ) + (tlWOneXP5c18 f ξ + tlWOneXP5c19 f ξ)))) +
        tlWOneXP5c20 f ξ))) := by sorry
