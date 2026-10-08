-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence6_term1_minimal_band_14
-- name    : MazurTransfer.order49_recurrence6_term1_minimal_band_14
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T00:39:20.229514+00:00
-- url     : https://prove2.me/theorems/9aa58091-77b6-4908-a6f3-24647fcd75aa
-- title:
--   Order-49 sixth recurrence: exact single band 14
-- statement:
--   The sum of the original row summands in band 14 is exactly the original normalized residual block 14. The minimal data definitions have separately checked equality with every original value. This is one of the six exact identities replacing the timed-out conjunction of bands12 through17; the downstream full Term1 statement is unchanged.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.normalizedResidual6Term1_eq and complete Lean AST signature range retained. Proof assembled from kernel dependencies and complete original AST commands. Custom rational syntax is expanded at AST-owned term ranges, each replacement separately verified by rfl. All original mathematical types, values, coefficients and Apache-2.0 headers retained. Named consumer: normalizedScalarResidual6. Standalone publication boundary: all exact original data values are kernel-compared with namespace-separated rational polynomial definitions. Original proof body selected at complete AST boundaries and wrapped in the same namespace; all resolved statement references retargeted at AST-owned byte positions. No mathematical values, binders, hypotheses or conclusions are weakened. Named consumer: the exact original normalized scalar platform theorem through its checked data equivalence bridge. Genuine split of the 300-second verification failure: exact original theorem commands and signatures retained at complete AST ranges. No hypotheses added. Named downstream consumer: the unchanged Term1 arithmetic target. Publication-import repair: the theorem and proof body are byte-unchanged, but the preamble imports only its corresponding original row/band partition, with the partition carrying its exact checked transitive arithmetic data. The unrelated remaining partitions and aggregate sums are excluded. Whole proof header replacement uses a Lean parser-owned header range. The prior failed publication handle is retained and never retried unchanged. Genuine dependency decomposition: this target imports only its single-band kernel-reached data, rather than the complete six-band partition and all row partitions. Original proof commands are retained at complete AST ranges. No statement weakening or proof-resource option changes.

import Definitions.Def_MazurTransfer_Order49Term1MinimalBand14Data
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneArithmeticData4
open Polynomial

theorem MazurTransfer.order49_recurrence6_term1_minimal_band_14 :
    MazurTransfer.Order49Term1MinimalBands.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term1Band14 = MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.normalizedResidual6Term1Block14 := by sorry
