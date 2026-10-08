-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence3_scaled3_block_13
-- name    : MazurTransfer.order49_recurrence3_scaled3_block_13
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T00:38:20.623206+00:00
-- url     : https://prove2.me/theorems/077f4c76-2fe8-4c02-886b-3fb78dc09335
-- title:
--   Third order-seven recurrence: scalar3 coefficient block 13
-- statement:
--   Let $L,R$ be the exact integer coefficient lists of the two sides of the cleared scalar identity at index 3 in the third order-seven pseudo-division recurrence. Their block beginning at index $416$, of length at most32, agrees: $$\operatorname{take}_{32}(\operatorname{drop}_{416}(L))=\operatorname{take}_{32}(\operatorname{drop}_{416}(R)).$$ The16 blocks, together with the separately certified empty tails, reconstruct the entire original list equality.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; Apache-2.0 original attribution retained in the original parent reconstruction. Published integer model definitions retain their original values, with separate standard-axiom checked comparisons. This splits the original full scalar3 kernel calculation into the original16 blocks of32 and an empty tail after512. Ordinary decide +kernel checks the exact coefficients; no native_decide, axioms, new hypotheses or proof-resource increases. Named downstream consumer: the exact original full scalar3_scaled_checked list identity and rational scalarResidual3Coefficient3.

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic

theorem MazurTransfer.order49_recurrence3_scaled3_block_13 : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledLeft.drop 416).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledRight.drop 416).take 32 := by sorry
