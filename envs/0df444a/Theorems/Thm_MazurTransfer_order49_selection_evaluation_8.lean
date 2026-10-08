-- Prove2me | Theorems.Thm_MazurTransfer_order49_selection_evaluation_8
-- name    : MazurTransfer.order49_selection_evaluation_8
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T23:59:20.213537+00:00
-- url     : https://prove2.me/theorems/23c4d982-c5bd-4cd1-9ca4-c7d062025803
-- title:
--   Order-49 selection factorization at abscissa 8
-- statement:
--   For every rational parameter $d$, let $S_d$ be the cleared Tate selection expression, $K_d$ the dual-kernel cubic, and $C_d$ the recorded degree-33 selection cofactor. At the rational abscissa $t=8$, the exact identity is $$S_d(t)=64^3 K_d(t)C_d(t).$$ This retains the original universal parameter statement. The37 evaluations at the distinct abscissae $0,\ldots,36$ supply the original degree-36 polynomial identity by interpolation.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0 original headers retained. Original MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.selectionEvalAt8 and its complete helper proof commands selected by kernel dependencies and original Lean AST byte ranges. The exact original selection interface has separately checked value comparisons; published original cofactor tables reused. No changed coefficients, parameters, hypotheses, tactics or proof-resource options. Named downstream consumers: the original selection_eval_fin/interpolation proof, full three-bounded-resultant theorem, and full arbitrary-E order49 exclusion.

import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData

theorem MazurTransfer.order49_selection_evaluation_8 (d : ℚ) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate d 8 := by sorry
