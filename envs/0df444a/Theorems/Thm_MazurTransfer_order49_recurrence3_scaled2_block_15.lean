-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence3_scaled2_block_15
-- name    : MazurTransfer.order49_recurrence3_scaled2_block_15
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T00:40:15.107341+00:00
-- url     : https://prove2.me/theorems/51a116dc-ae0b-45d9-81c0-991feaaa35bd
-- title:
--   Third order-seven recurrence: scalar2 coefficient block 15
-- statement:
--   Let $L,R$ be the exact integer coefficient lists of the two sides of the cleared scalar identity at index 2 in the third order-seven pseudo-division recurrence. Their block beginning at index $480$, of length at most32, agrees: $$\operatorname{take}_{32}(\operatorname{drop}_{480}(L))=\operatorname{take}_{32}(\operatorname{drop}_{480}(R)).$$ The16 blocks, together with the separately certified empty tails, reconstruct the entire original list equality.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; Apache-2.0 original attribution retained in the original parent reconstruction. Published integer model definitions retain their original values, with separate standard-axiom checked comparisons. This splits the original full scalar2 kernel calculation into the original16 blocks of32 and an empty tail after512. Ordinary decide +kernel checks the exact coefficients; no native_decide, axioms, new hypotheses or proof-resource increases. Named downstream consumer: the exact original full scalar2_scaled_checked list identity and rational scalarResidual3Coefficient2.

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic

theorem MazurTransfer.order49_recurrence3_scaled2_block_15 : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledLeft.drop 480).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledRight.drop 480).take 32 := by sorry
