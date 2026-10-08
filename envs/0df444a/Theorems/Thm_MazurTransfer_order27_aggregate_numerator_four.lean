-- Prove2me | Theorems.Thm_MazurTransfer_order27_aggregate_numerator_four
-- name    : MazurTransfer.order27_aggregate_numerator_four
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T15:08:25.295976+00:00
-- url     : https://prove2.me/theorems/9dd1b4c9-21a5-4fbc-b762-955a5749349b
-- title:
--   Order-27 kernel-cubic numerator: four
-- statement:
--   Let $f,\xi\in\mathbb Q$ satisfy the fixed trisection equation $T(f,\xi)=0$. The displayed term of the kernel-cubic numerator equals the displayed complete sum of fixed polynomial remainder blocks. This is the full original tl_mnum₄ identity, with its original hypotheses and coefficient functions. The downstream consumer combines the four numerator terms and their zero sum to obtain $M(f,N(f,\xi)/D(f,\xi))=0$ when $D(f,\xi)\ne0$. No rational-point existence or torsion exclusion is assumed.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Full signatures extracted using Lean signature AST ranges; proof commands retained by kernel dependencies and resolved references. This is an exact split of the terminal timed-out kernel coordinate verification, preserving the original hypotheses and conclusion. Original Apache-2.0 file headers retained.

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData4
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5

open MazurTorsion.Kubert

theorem MazurTransfer.order27_aggregate_numerator_four :
(∀ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0),
-(f * (f - 1) * (f ^ 15 + 24 * f ^ 14 - 191 * f ^ 13 + 768 * f ^ 12 - 2105 * f ^ 11 + 4341 * f
      ^ 10 - 7010 * f ^ 9 + 9075 * f ^ 8 - 9491 * f ^ 7 + 7985 * f ^ 6 - 5312 * f ^ 5 + 2713 * f ^
      4 - 1020 * f ^ 3 + 259 * f ^ 2 - 39 * f + 1)) * (tlD0 f ξ + tlD1 f ξ) ^ 3 =
      ((((((tlWZeroXP0c0 f ξ + tlWZeroXP0c1 f ξ) + (tlWZeroXP0c2 f ξ + tlWZeroXP0c3 f ξ)) +
        ((tlWZeroXP0c4 f ξ + tlWZeroXP0c5 f ξ) + (tlWZeroXP0c6 f ξ + tlWZeroXP0c7 f ξ))) +
        (((tlWZeroXP0c8 f ξ + tlWZeroXP0c9 f ξ) + (tlWZeroXP0c10 f ξ + tlWZeroXP0c11 f ξ)) +
        ((tlWZeroXP0c12 f ξ + tlWZeroXP0c13 f ξ) + (tlWZeroXP0c14 f ξ + tlWZeroXP0c15 f ξ)))) +
        ((((tlWZeroXP0c16 f ξ + tlWZeroXP1c0 f ξ) + (tlWZeroXP1c1 f ξ + tlWZeroXP1c2 f ξ)) +
        ((tlWZeroXP1c3 f ξ + tlWZeroXP1c4 f ξ) + (tlWZeroXP1c5 f ξ + tlWZeroXP1c6 f ξ))) +
        (((tlWZeroXP1c7 f ξ + tlWZeroXP1c8 f ξ) + (tlWZeroXP1c9 f ξ + tlWZeroXP1c10 f ξ)) +
        ((tlWZeroXP1c11 f ξ + tlWZeroXP1c12 f ξ) + (tlWZeroXP1c13 f ξ + tlWZeroXP1c14 f ξ))))) +
        (((((tlWZeroXP1c15 f ξ + tlWZeroXP1c16 f ξ) + (tlWZeroXP1c17 f ξ + tlWZeroXP1c18 f ξ)) +
        ((tlWZeroXP2c0 f ξ + tlWZeroXP2c1 f ξ) + (tlWZeroXP2c2 f ξ + tlWZeroXP2c3 f ξ))) +
        (((tlWZeroXP2c4 f ξ + tlWZeroXP2c5 f ξ) + (tlWZeroXP2c6 f ξ + tlWZeroXP2c7 f ξ)) +
        ((tlWZeroXP2c8 f ξ + tlWZeroXP2c9 f ξ) + (tlWZeroXP2c10 f ξ + tlWZeroXP2c11 f ξ)))) +
        ((((tlWZeroXP2c12 f ξ + tlWZeroXP2c13 f ξ) + (tlWZeroXP2c14 f ξ + tlWZeroXP2c15 f ξ)) +
        ((tlWZeroXP2c16 f ξ + tlWZeroXP2c17 f ξ) + (tlWZeroXP2c18 f ξ + tlWZeroXP2c19 f ξ))) +
        (((tlWZeroXP3c0 f ξ + tlWZeroXP3c1 f ξ) + (tlWZeroXP3c2 f ξ + tlWZeroXP3c3 f ξ)) +
        ((tlWZeroXP3c4 f ξ + tlWZeroXP3c5 f ξ) + (tlWZeroXP3c6 f ξ + tlWZeroXP3c7 f ξ)))))) +
        (((tlWZeroXP3c8 f ξ + tlWZeroXP3c9 f ξ) + (tlWZeroXP3c10 f ξ + tlWZeroXP3c11 f ξ)) +
        ((tlWZeroXP3c12 f ξ + tlWZeroXP3c13 f ξ) + (tlWZeroXP3c14 f ξ + tlWZeroXP3c15 f ξ)))) := by sorry
