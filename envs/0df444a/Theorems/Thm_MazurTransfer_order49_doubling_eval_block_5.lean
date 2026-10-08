-- Prove2me | Theorems.Thm_MazurTransfer_order49_doubling_eval_block_5
-- name    : MazurTransfer.order49_doubling_eval_block_5
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T02:40:38.099625+00:00
-- url     : https://prove2.me/theorems/1c4b8829-753d-4e39-b8a2-bf362c268aa0
-- title:
--   Order-seven doubling: evaluation block 5
-- statement:
--   For every rational parameter $d$ and every integer index $i$ with $0 \le i < 4$, the two degree-28 homogeneous doubling expressions have equal values at the rational abscissa $20+i$.
--
--   This supplies one exact interpolation block for the corresponding polynomial identity used in the exclusion of rational points of order $49$.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.evalBlock5. Original module MazurTorsion.Kubert.OrderSevenIsogenyDoublingCertificateEval5; complete Lean AST signature ranges and all original hypotheses preserved. Apache-2.0 headers and attribution retained. Named downstream consumer: homogeneous doubling identity or quotient-prePsi-seven factorization, then the full every-curve order49 exclusion.

import Definitions.Def_MazurTransfer_Order49DirectEvaluationPredicates
open Polynomial

theorem MazurTransfer.order49_doubling_eval_block_5 (d : ℚ) (i : Fin 4) :
    MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal.EvalCertificate d ((i : ℚ) + 20) := by sorry
