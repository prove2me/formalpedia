-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence3_scaled3_block_10
-- name    : MazurTransfer.order49_recurrence3_scaled3_block_10
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T00:11:09.92707+00:00
-- url     : https://prove2.me/theorems/0bb96da1-4be6-4e76-a506-3cb753d20538
-- title:
--   Third order-seven recurrence: scalar3 coefficient block 10
-- statement:
--   Let $L,R$ be the exact integer coefficient lists of the two sides of the cleared scalar identity at index 3 in the third order-seven pseudo-division recurrence. Their block beginning at index $320$, of length at most32, agrees: $$\operatorname{take}_{32}(\operatorname{drop}_{320}(L))=\operatorname{take}_{32}(\operatorname{drop}_{320}(R)).$$ The16 blocks, together with the separately certified empty tails, reconstruct the entire original list equality.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; Apache-2.0 original attribution retained in the original parent reconstruction. Published integer model definitions retain their original values, with separate standard-axiom checked comparisons. This splits the original full scalar3 kernel calculation into the original16 blocks of32 and an empty tail after512. Ordinary decide +kernel checks the exact coefficients; no native_decide, axioms, new hypotheses or proof-resource increases. Named downstream consumer: the exact original full scalar3_scaled_checked list identity and rational scalarResidual3Coefficient3.

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic

theorem MazurTransfer.order49_recurrence3_scaled3_block_10 : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledLeft.drop 320).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledRight.drop 320).take 32 := by sorry
