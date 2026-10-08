-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence4_exact_integer_exceptional
-- name    : MazurTransfer.order49_recurrence4_exact_integer_exceptional
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T12:03:17.459574+00:00
-- url     : https://prove2.me/theorems/961db9fe-9002-41f4-b985-dccae1b843a8
-- title:
--   Fourth recurrence: exact reused integer certificate exceptional
-- statement:
--   Establish the unconditional exact denominator-cleared arithmetic identity for original fourth-recurrence coefficient exceptional. The proof-free generic equality certificate retains the full equality. Integer tables alias the previously verified exact third- and fifth-recurrence tables; no coefficient is changed.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0. Ordinary kernel computations or polynomial normalization check this closed identity. Named downstream consumer: the unchanged original scalarResidual4Coefficientexceptional rational-polynomial statement (exceptional interpretation feeds all three), original recurrence4 and full every-curve order49 exclusion. The numerical extractor is tooling only and provides no proof.

import Definitions.Def_MazurTransfer_Order49Recurrence4ReusedDenseIntegerDataWithExtraTables
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData4
import Definitions.Def_MazurTransfer_ExactEqualityCertificate
open Polynomial

theorem MazurTransfer.order49_recurrence4_exact_integer_exceptional : MazurTransfer.ExactEqualityCertificate (α := Polynomial ℚ) (C (MazurTransfer.Order49Recurrence4DenseCandidate.denominator : ℚ) * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional4) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence4DenseCandidate.exceptionalNumerator) := by sorry
