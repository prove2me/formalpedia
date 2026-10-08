-- Prove2me | Theorems.Thm_MazurTransfer_order49_doubling_eval_block_1
-- name    : MazurTransfer.order49_doubling_eval_block_1
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T02:40:38.227229+00:00
-- url     : https://prove2.me/theorems/36d4b16a-0516-45da-8721-905143c48a7e
-- title:
--   Order-seven doubling: evaluation block 1
-- statement:
--   For every rational parameter $d$ and every integer index $i$ with $0 \le i < 4$, the two degree-28 homogeneous doubling expressions have equal values at the rational abscissa $4+i$.
--
--   This supplies one exact interpolation block for the corresponding polynomial identity used in the exclusion of rational points of order $49$.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock1. Original module MazurTorsion.Kubert.OrderSevenIsogenyDoublingCertificateEval1; complete Lean AST signature ranges and all original hypotheses preserved. Apache-2.0 headers and attribution retained. Named downstream consumer: homogeneous doubling identity or quotient-prePsi-seven factorization, then the full every-curve order49 exclusion.

import Definitions.Def_MazurTransfer_Order49DirectEvaluationPredicates
open Polynomial

theorem MazurTransfer.order49_doubling_eval_block_1 (d : ℚ) (i : Fin 4) :
    MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate d ((i : ℚ) + 4) := by sorry
