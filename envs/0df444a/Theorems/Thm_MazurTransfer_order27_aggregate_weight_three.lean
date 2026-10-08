-- Prove2me | Theorems.Thm_MazurTransfer_order27_aggregate_weight_three
-- name    : MazurTransfer.order27_aggregate_weight_three
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T15:05:38.103077+00:00
-- url     : https://prove2.me/theorems/557792ad-5ed1-4b52-b0ca-0a591b40ab0c
-- title:
--   Order-27 third-leg aggregation: weight three
-- statement:
--   The displayed equalities hold for every rational family parameter and coordinate under their displayed kernel-cubic hypotheses. They are the complete original zlWThree_val identities, expressed using the fixed polynomial coefficient functions. The downstream consumer combines these products, coefficients, weighted terms and their vanishing sum to prove the original third-leg polynomial identity. No rational-point existence or torsion exclusion is assumed.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Full signatures extracted using Lean signature AST ranges; proof commands retained by kernel dependencies and resolved references. This is an exact split of the terminal timed-out third-leg polynomial verification, preserving the original hypotheses and conclusion. Original Apache-2.0 file headers retained.

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5

open MazurTorsion.Kubert

theorem MazurTransfer.order27_aggregate_weight_three :
(∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
((zlTNCbP0c0 f + zlTNCbP0c1 f) + zlTNCbP0c2 f) * zlCThree0 f =
      (zlWThreeP0c0 f + zlWThreeP0c1 f) + (zlWThreeP0c2 f + zlWThreeP0c3 f)) := by sorry
