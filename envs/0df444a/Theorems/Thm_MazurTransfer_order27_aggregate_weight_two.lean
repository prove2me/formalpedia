-- Prove2me | Theorems.Thm_MazurTransfer_order27_aggregate_weight_two
-- name    : MazurTransfer.order27_aggregate_weight_two
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T15:05:34.90741+00:00
-- url     : https://prove2.me/theorems/c9560b24-b365-4ecd-abc5-78a88a98b650
-- title:
--   Order-27 third-leg aggregation: weight two
-- statement:
--   The displayed equalities hold for every rational family parameter and coordinate under their displayed kernel-cubic hypotheses. They are the complete original zlWTwo_val identities, expressed using the fixed polynomial coefficient functions. The downstream consumer combines these products, coefficients, weighted terms and their vanishing sum to prove the original third-leg polynomial identity. No rational-point existence or torsion exclusion is assumed.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Full signatures extracted using Lean signature AST ranges; proof commands retained by kernel dependencies and resolved references. This is an exact split of the terminal timed-out third-leg polynomial verification, preserving the original hypotheses and conclusion. Original Apache-2.0 file headers retained.

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5

open MazurTorsion.Kubert

theorem MazurTransfer.order27_aggregate_weight_two :
(∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(((zlTNSqTDP0c0 f Z + zlTNSqTDP0c1 f Z) + (zlTNSqTDP0c2 f Z + zlTNSqTDP0c3 f Z)) +
      ((zlTNSqTDP0c4 f Z + zlTNSqTDP0c5 f Z) + (zlTNSqTDP0c6 f Z + zlTNSqTDP0c7 f Z))) * zlCTwo0 f
      =
      (((zlWTwoP0c0 f Z + zlWTwoP0c1 f Z) + (zlWTwoP0c2 f Z + zlWTwoP0c3 f Z)) +
        ((zlWTwoP0c4 f Z + zlWTwoP0c5 f Z) + (zlWTwoP0c6 f Z + zlWTwoP0c7 f Z))) +
        (zlWTwoP0c8 f Z + zlWTwoP0c9 f Z)) := by sorry
