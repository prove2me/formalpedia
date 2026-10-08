-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence5_exact_integer_field_10
-- name    : MazurTransfer.order49_recurrence5_exact_integer_field_10
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T12:08:38.445022+00:00
-- url     : https://prove2.me/theorems/39271d0f-4a2a-4223-bb19-31293c54621f
-- title:
--   Fifth recurrence: exact arithmetic identity 10
-- statement:
--   Prove identity 10 from the complete eleven-identity fifth-recurrence integer certificate. The exact registered parent field type is unchanged and independently kernel compared with this statement. This is a mandatory unconditional identity, represented by the same proof-free generic equality certificate.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0. Exact field of registered parent MazurTransfer.order49_recurrence5_dense_integer_certificates_and_anchors, target 495a02ae-8bc1-434c-badb-357a6efb2d5a. The complete parent verification hit 300 seconds, so the actual typed conjunction fields are now independently proved. The field is extracted from the actual compiled declaration type and kernel-reflexivity compared with this copied statement; no text-based mathematical cuts are used. Named downstream consumers: the same full eleven-identity parent and unchanged original recurrence5 scalar statements.

import Definitions.Def_MazurTransfer_Order49Recurrence5DenseIntegerChunkDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Definitions.Def_MazurTransfer_Order49Recurrence3StandaloneDenseData3
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData5
import Definitions.Def_MazurTransfer_ExactEqualityCertificate
open Polynomial

theorem MazurTransfer.order49_recurrence5_exact_integer_field_10 : @MazurTransfer.ExactEqualityCertificate (@Polynomial Rat Rat.semiring)
  (@HMul.hMul (@Polynomial Rat Rat.semiring)
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient
    (@Polynomial Rat Rat.semiring) (@instHMul (@Polynomial Rat Rat.semiring) (@Polynomial.instMul Rat Rat.semiring))
    (@DFunLike.coe
      (@RingHom Rat (@Polynomial Rat Rat.semiring) (@Semiring.toNonAssocSemiring Rat Rat.semiring)
        (@Semiring.toNonAssocSemiring (@Polynomial Rat Rat.semiring) (@Polynomial.semiring Rat Rat.semiring)))
      Rat (fun x => @Polynomial Rat Rat.semiring)
      (@RingHom.instFunLike Rat (@Polynomial Rat Rat.semiring) (@Semiring.toNonAssocSemiring Rat Rat.semiring)
        (@Semiring.toNonAssocSemiring (@Polynomial Rat Rat.semiring) (@Polynomial.semiring Rat Rat.semiring)))
      (@Polynomial.C Rat Rat.semiring)
      (@Int.cast Rat Rat.instIntCast MazurTransfer.Order49Recurrence5DenseCandidate.denominator))
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional5)
  (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial
    MazurTransfer.Order49Recurrence5DenseCandidate.exceptionalNumerator) := by sorry
