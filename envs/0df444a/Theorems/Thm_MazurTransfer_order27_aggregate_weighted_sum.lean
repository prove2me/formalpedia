-- Prove2me | Theorems.Thm_MazurTransfer_order27_aggregate_weighted_sum
-- name    : MazurTransfer.order27_aggregate_weighted_sum
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T15:05:59.011527+00:00
-- url     : https://prove2.me/theorems/56349043-7ff6-4386-842a-b1ba1b8dae63
-- title:
--   Order-27 third-leg aggregation: weighted sum
-- statement:
--   The displayed equalities hold for every rational family parameter and coordinate under their displayed kernel-cubic hypotheses. They are the complete original zl_zeroZ identities, expressed using the fixed polynomial coefficient functions. The downstream consumer combines these products, coefficients, weighted terms and their vanishing sum to prove the original third-leg polynomial identity. No rational-point existence or torsion exclusion is assumed.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Full signatures extracted using Lean signature AST ranges; proof commands retained by kernel dependencies and resolved references. This is an exact split of the terminal timed-out third-leg polynomial verification, preserving the original hypotheses and conclusion. Original Apache-2.0 file headers retained.

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5

open MazurTorsion.Kubert

theorem MazurTransfer.order27_aggregate_weighted_sum :
(∀ (f Z : ℚ),
(zlWThreeP0c0 f + zlWThreeP0c1 f) + (zlWThreeP0c2 f + zlWThreeP0c3 f) + (((zlWTwoP0c0 f Z +
      zlWTwoP0c1 f Z) + (zlWTwoP0c2 f Z + zlWTwoP0c3 f Z)) + ((zlWTwoP0c4 f Z + zlWTwoP0c5 f Z) +
      (zlWTwoP0c6 f Z + zlWTwoP0c7 f Z))) + (zlWTwoP0c8 f Z + zlWTwoP0c9 f Z) + ((((zlWOneP0c0 f Z
      + zlWOneP0c1 f Z) + (zlWOneP0c2 f Z + zlWOneP0c3 f Z)) + ((zlWOneP0c4 f Z + zlWOneP0c5 f Z)
      + (zlWOneP0c6 f Z + zlWOneP0c7 f Z))) + (((zlWOneP0c8 f Z + zlWOneP1c0 f Z) + (zlWOneP1c1 f
      Z + zlWOneP1c2 f Z)) + ((zlWOneP1c3 f Z + zlWOneP1c4 f Z) + (zlWOneP1c5 f Z + zlWOneP1c6 f
      Z)))) + ((((zlWOneP1c7 f Z + zlWOneP1c8 f Z) + (zlWOneP1c9 f Z + zlWOneP2c0 f Z)) +
      ((zlWOneP2c1 f Z + zlWOneP2c2 f Z) + (zlWOneP2c3 f Z + zlWOneP2c4 f Z))) + zlWOneP2c5 f Z) +
      (((zlWZeroP0c0 f Z + zlWZeroP0c1 f Z) + (zlWZeroP0c2 f Z + zlWZeroP0c3 f Z)) + ((zlWZeroP0c4
      f Z + zlWZeroP0c5 f Z) + (zlWZeroP0c6 f Z + zlWZeroP0c7 f Z))) + (((zlWZeroP1c0 f Z +
      zlWZeroP1c1 f Z) + (zlWZeroP1c2 f Z + zlWZeroP1c3 f Z)) + zlWZeroP1c4 f Z) = 0) := by sorry
