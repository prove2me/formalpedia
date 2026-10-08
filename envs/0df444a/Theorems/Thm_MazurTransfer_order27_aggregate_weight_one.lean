-- Prove2me | Theorems.Thm_MazurTransfer_order27_aggregate_weight_one
-- name    : MazurTransfer.order27_aggregate_weight_one
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T15:05:41.058255+00:00
-- url     : https://prove2.me/theorems/b3fda9a1-388a-4e91-92b2-576f091d1454
-- title:
--   Order-27 third-leg aggregation: weight one
-- statement:
--   The displayed equalities hold for every rational family parameter and coordinate under their displayed kernel-cubic hypotheses. They are the complete original zlWOne_val identities, expressed using the fixed polynomial coefficient functions. The downstream consumer combines these products, coefficients, weighted terms and their vanishing sum to prove the original third-leg polynomial identity. No rational-point existence or torsion exclusion is assumed.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Full signatures extracted using Lean signature AST ranges; proof commands retained by kernel dependencies and resolved references. This is an exact split of the terminal timed-out third-leg polynomial verification, preserving the original hypotheses and conclusion. Original Apache-2.0 file headers retained.

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5

open MazurTorsion.Kubert

theorem MazurTransfer.order27_aggregate_weight_one :
(∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(((((zlTNTDSqP0c0 f Z + zlTNTDSqP0c1 f Z) + (zlTNTDSqP0c2 f Z + zlTNTDSqP0c3 f Z)) +
      ((zlTNTDSqP0c4 f Z + zlTNTDSqP1c0 f Z) + (zlTNTDSqP1c1 f Z + zlTNTDSqP1c2 f Z))) +
      (((zlTNTDSqP1c3 f Z + zlTNTDSqP1c4 f Z) + (zlTNTDSqP1c5 f Z + zlTNTDSqP2c0 f Z)) +
      ((zlTNTDSqP2c1 f Z + zlTNTDSqP2c2 f Z) + (zlTNTDSqP2c3 f Z + zlTNTDSqP2c4 f Z)))) +
      (((zlTNTDSqP3c0 f Z + zlTNTDSqP3c1 f Z) + (zlTNTDSqP3c2 f Z + zlTNTDSqP3c3 f Z)) +
      (zlTNTDSqP3c4 f Z + zlTNTDSqP3c5 f Z))) * zlCOne0 f =
      ((((zlWOneP0c0 f Z + zlWOneP0c1 f Z) + (zlWOneP0c2 f Z + zlWOneP0c3 f Z)) +
        ((zlWOneP0c4 f Z + zlWOneP0c5 f Z) + (zlWOneP0c6 f Z + zlWOneP0c7 f Z))) +
        (((zlWOneP0c8 f Z + zlWOneP1c0 f Z) + (zlWOneP1c1 f Z + zlWOneP1c2 f Z)) +
        ((zlWOneP1c3 f Z + zlWOneP1c4 f Z) + (zlWOneP1c5 f Z + zlWOneP1c6 f Z)))) +
        ((((zlWOneP1c7 f Z + zlWOneP1c8 f Z) + (zlWOneP1c9 f Z + zlWOneP2c0 f Z)) +
        ((zlWOneP2c1 f Z + zlWOneP2c2 f Z) + (zlWOneP2c3 f Z + zlWOneP2c4 f Z))) +
        zlWOneP2c5 f Z)) := by sorry
