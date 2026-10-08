-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence4_exact_integer_0
-- name    : MazurTransfer.order49_recurrence4_exact_integer_0
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T12:13:29.325069+00:00
-- url     : https://prove2.me/theorems/6889802f-1a79-40c8-9438-7072244d6787
-- title:
--   Fourth recurrence: exact reused integer certificate 0
-- statement:
--   Establish the unconditional exact denominator-cleared arithmetic identity for original fourth-recurrence coefficient 0. The proof-free generic equality certificate retains the full equality. Integer tables alias the previously verified exact third- and fifth-recurrence tables; no coefficient is changed.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0. Ordinary kernel computations or polynomial normalization check this closed identity. Named downstream consumer: the unchanged original scalarResidual4Coefficient0 rational-polynomial statement (exceptional interpretation feeds all three), original recurrence4 and full every-curve order49 exclusion. The numerical extractor is tooling only and provides no proof.

import Definitions.Def_MazurTransfer_Order49Recurrence4ReusedDenseIntegerDataWithExtraTables
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData4
import Definitions.Def_MazurTransfer_ExactEqualityCertificate
open Polynomial

theorem MazurTransfer.order49_recurrence4_exact_integer_0 : MazurTransfer.ExactEqualityCertificate (α := List ℤ) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scale MazurTransfer.Order49Recurrence4DenseCandidate.denominator (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul MazurTransfer.Order49Recurrence4DenseCandidate.leadingSquare MazurTransfer.Order49Recurrence4DenseCandidate.a0)) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.add (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scale MazurTransfer.Order49Recurrence4DenseCandidate.denominator (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul MazurTransfer.Order49Recurrence4DenseCandidate.b0 MazurTransfer.Order49Recurrence4DenseCandidate.quotientConstant)) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul MazurTransfer.Order49Recurrence4DenseCandidate.exceptionalProductNumerator MazurTransfer.Order49Recurrence4DenseCandidate.c0)) := by sorry
