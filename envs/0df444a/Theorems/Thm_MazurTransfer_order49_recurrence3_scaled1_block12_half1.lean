-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence3_scaled1_block12_half1
-- name    : MazurTransfer.order49_recurrence3_scaled1_block12_half1
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T00:39:53.180965+00:00
-- url     : https://prove2.me/theorems/95006345-86cb-46b3-aa2d-bd49571f5e46
-- title:
--   Third order-seven recurrence: scalar1 block12 half1
-- statement:
--   The exact16-entry block starting at coefficient 400 agrees between the original two integer coefficient lists. Together with the adjacent separately checked half, this gives the entire original32-entry block starting at coefficient 384. No coefficient is omitted.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; Apache-2.0 original attribution retained in the original parent reconstruction. Published integer model definitions retain their original values, with separate standard-axiom checked comparisons. This splits the failed full scalar1 kernel calculation into the original16 blocks of32 and an empty tail after512. Ordinary decide +kernel checks the exact coefficients; no native_decide, axioms, new hypotheses or proof-resource increases. Named downstream consumer: the exact original full scalar1_scaled_checked list identity and rational scalarResidual3Coefficient1. Genuine16-entry decomposition of a retained32-entry verification failure. The canonical32-entry target is reconstructed by the standard List.take_add theorem. The original full coefficient-list equality remains unchanged.

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic

theorem MazurTransfer.order49_recurrence3_scaled1_block12_half1 : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledLeft.drop 400).take 16 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledRight.drop 400).take 16 := by sorry
