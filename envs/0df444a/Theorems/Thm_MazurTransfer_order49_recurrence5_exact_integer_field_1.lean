-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence5_exact_integer_field_1
-- name    : MazurTransfer.order49_recurrence5_exact_integer_field_1
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T11:53:39.939707+00:00
-- url     : https://prove2.me/theorems/bf1f1d17-b236-4d1b-9bc4-b273d94d5f4e
-- title:
--   Fifth recurrence: exact arithmetic identity 1
-- statement:
--   Prove identity 1 from the complete eleven-identity fifth-recurrence integer certificate. The exact registered parent field type is unchanged and independently kernel compared with this statement. This is a mandatory unconditional identity, represented by the same proof-free generic equality certificate.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0. Exact field of registered parent MazurTransfer.order49_recurrence5_dense_integer_certificates_and_anchors, target 495a02ae-8bc1-434c-badb-357a6efb2d5a. The complete parent verification hit 300 seconds, so the actual typed conjunction fields are now independently proved. The field is extracted from the actual compiled declaration type and kernel-reflexivity compared with this copied statement; no text-based mathematical cuts are used. Named downstream consumers: the same full eleven-identity parent and unchanged original recurrence5 scalar statements.

import Definitions.Def_MazurTransfer_Order49Recurrence5DenseIntegerChunkDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Definitions.Def_MazurTransfer_Order49Recurrence3StandaloneDenseData3
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData5
import Definitions.Def_MazurTransfer_ExactEqualityCertificate
open Polynomial

theorem MazurTransfer.order49_recurrence5_exact_integer_field_1 : @MazurTransfer.ExactEqualityCertificate (List Int)
  (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul
    MazurTransfer.Order49Recurrence5DenseCandidate.a3 MazurTransfer.Order49Recurrence5DenseCandidate.a3)
  MazurTransfer.Order49Recurrence5DenseCandidate.a3Square := by sorry
