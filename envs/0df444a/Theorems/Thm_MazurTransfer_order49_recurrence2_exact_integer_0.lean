-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence2_exact_integer_0
-- name    : MazurTransfer.order49_recurrence2_exact_integer_0
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T13:05:38.670974+00:00
-- url     : https://prove2.me/theorems/633607d7-f578-4ecd-9939-9494fd5e4938
-- title:
--   Second recurrence: exact complete integer coefficient identity 0
-- statement:
--   The complete denominator-cleared second-recurrence integer identity for coefficient 0. The left coefficient list has its single trailing zero written explicitly, matching the cancelling highest coefficient on the right. All coefficients and original exceptional factors are retained. Appending a zero preserves the interpreted polynomial, so this supplies the full original rational-polynomial scalar equality.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0. Dividends have exact complete original table interpretations, and divisor/remainder tables reuse the independently verified third-recurrence tables. Five shared intermediate lists have independently checked closed exact value proofs. Ordinary kernel computation proves this complete padded list equality. The zero-padding step has a separate generic polynomial interpretation proof in the downstream consumer; the original rational-polynomial theorem statement is unchanged. The earlier unpadded equality was only an unpublished local candidate and correctly failed due to one trailing zero. Named downstream consumers: unchanged original scalarResidual2Coefficient0, recurrence2 and full every-curve order49 exclusion. No roadmap weights or original challenge statements are changed.

import Definitions.Def_MazurTransfer_Order49Recurrence2ReusedDenseIntegerData
import Definitions.Def_MazurTransfer_ExactEqualityCertificate

theorem MazurTransfer.order49_recurrence2_exact_integer_0 : MazurTransfer.ExactEqualityCertificate (α := List ℤ) ((MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scale MazurTransfer.Order49Recurrence2DenseCandidate.denominator (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul MazurTransfer.Order49Recurrence2DenseCandidate.leadingSquare MazurTransfer.Order49Recurrence2DenseCandidate.a0)) ++ [0]) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.add (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scale MazurTransfer.Order49Recurrence2DenseCandidate.denominator (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul MazurTransfer.Order49Recurrence2DenseCandidate.b0 MazurTransfer.Order49Recurrence2DenseCandidate.quotientConstant)) (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.mul MazurTransfer.Order49Recurrence2DenseCandidate.exceptionalProductNumerator MazurTransfer.Order49Recurrence2DenseCandidate.c0)) := by sorry
