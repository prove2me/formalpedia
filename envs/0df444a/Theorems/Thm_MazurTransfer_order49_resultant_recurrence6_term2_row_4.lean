-- Prove2me | Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_term2_row_4
-- name    : MazurTransfer.order49_resultant_recurrence6_term2_row_4
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T22:17:53.430445+00:00
-- url     : https://prove2.me/theorems/226346f5-feeb-4d1a-84a1-20d9307d66fd
-- title:
--   Order-49 Term2 row identities 4–5
-- statement:
--   Work in the rational polynomial ring $\mathbb Q[D]$ with the fixed original row and band data. For each index $i=4,\ldots,5$, the fixed input coefficient block $b_i$ and inner polynomial $I$ satisfy $b_iI=R_i$, where $R_i$ is the corresponding exact product row. These unconditional finite identities are used to establish the exact original product identity $B_0I=T_2$; no product identity or torsion hypothesis is assumed.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original theorem MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.normalizedResidual6Term2_eq and complete Lean AST signature range retained. Proof assembled from kernel dependencies and complete original AST commands. Custom rational syntax is expanded at AST-owned term ranges, each replacement separately verified by rfl. All original mathematical types, values, coefficients and Apache-2.0 headers retained. Named consumer: normalizedScalarResidual6. Standalone publication boundary: all exact original data values are kernel-compared with namespace-separated rational polynomial definitions. Original proof body selected at complete AST boundaries and wrapped in the same namespace; all resolved statement references retargeted at AST-owned byte positions. No mathematical values, binders, hypotheses or conclusions are weakened. Named consumer: the exact original normalized scalar platform theorem through its checked data equivalence bridge. Genuine split of the 300-second verification failure: exact original theorem commands and signatures retained at complete AST ranges. No hypotheses added. Named downstream consumer: the unchanged Term2 arithmetic target. Publication-import repair: the theorem and proof body are byte-unchanged, but the preamble imports only its corresponding original row/band partition, with the partition carrying its exact checked transitive arithmetic data. The unrelated remaining partitions and aggregate sums are excluded. Whole proof header replacement uses a Lean parser-owned header range. The prior failed publication handle is retained and never retried unchanged.

import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneTerm2Partition2
open Polynomial
open MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

theorem MazurTransfer.order49_resultant_recurrence6_term2_row_4 :
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0NormalizedBlock4 * MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.normalizedResidual6Inner =
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term2Row4) ∧
(MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0NormalizedBlock5 * MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.normalizedResidual6Inner =
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence6Term2Row5) := by sorry
