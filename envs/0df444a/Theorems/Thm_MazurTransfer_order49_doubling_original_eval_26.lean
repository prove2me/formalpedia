-- Prove2me | Theorems.Thm_MazurTransfer_order49_doubling_original_eval_26
-- name    : MazurTransfer.order49_doubling_original_eval_26
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T03:14:45.038026+00:00
-- url     : https://prove2.me/theorems/8e81dec6-16e5-43ad-b660-82897cb487c5
-- title:
--   Order-seven doubling: original evaluation at 26
-- statement:
--   For every rational parameter d, the exact original doubling polynomial evaluation certificate holds at the rational abscissa 26. This is one unchanged individual evaluation lemma from the original interpolation block.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Exact original _private.MazurTorsion.Kubert.OrderSevenIsogenyDoublingCertificateEval6.0.MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.eval_26; original Lean AST signature and every hypothesis preserved. Apache-2.0. Named downstream consumer: original MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock6, then the exact polynomial aggregate and full every-curve order49 exclusion.

import Definitions.Def_MazurTransfer_Order49DirectEvaluationPredicates
open Polynomial

theorem MazurTransfer.order49_doubling_original_eval_26 (d : ℚ) : MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate d 26 := by sorry
