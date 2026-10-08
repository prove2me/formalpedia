-- Prove2me | Theorems.Thm_MazurTransfer_order27_aggregate_weight_zero
-- name    : MazurTransfer.order27_aggregate_weight_zero
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T15:05:46.740168+00:00
-- url     : https://prove2.me/theorems/92e33ba9-0491-4709-9eb6-5dc4d598458b
-- title:
--   Order-27 third-leg aggregation: weight zero
-- statement:
--   The displayed equalities hold for every rational family parameter and coordinate under their displayed kernel-cubic hypotheses. They are the complete original zlWZero_val identities, expressed using the fixed polynomial coefficient functions. The downstream consumer combines these products, coefficients, weighted terms and their vanishing sum to prove the original third-leg polynomial identity. No rational-point existence or torsion exclusion is assumed.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Full signatures extracted using Lean signature AST ranges; proof commands retained by kernel dependencies and resolved references. This is an exact split of the terminal timed-out third-leg polynomial verification, preserving the original hypotheses and conclusion. Original Apache-2.0 file headers retained.

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5

open MazurTorsion.Kubert

theorem MazurTransfer.order27_aggregate_weight_zero :
(∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
((((zlTDCbP0c0 f Z + zlTDCbP0c1 f Z) + (zlTDCbP0c2 f Z + zlTDCbP0c3 f Z)) + ((zlTDCbP0c4 f Z +
      zlTDCbP1c0 f Z) + (zlTDCbP1c1 f Z + zlTDCbP1c2 f Z))) + ((zlTDCbP1c3 f Z + zlTDCbP1c4 f Z) +
      zlTDCbP1c5 f Z)) * zlCZero0 f =
      (((zlWZeroP0c0 f Z + zlWZeroP0c1 f Z) + (zlWZeroP0c2 f Z + zlWZeroP0c3 f Z)) +
        ((zlWZeroP0c4 f Z + zlWZeroP0c5 f Z) + (zlWZeroP0c6 f Z + zlWZeroP0c7 f Z))) +
        (((zlWZeroP1c0 f Z + zlWZeroP1c1 f Z) + (zlWZeroP1c2 f Z + zlWZeroP1c3 f Z)) +
        zlWZeroP1c4 f Z)) := by sorry
