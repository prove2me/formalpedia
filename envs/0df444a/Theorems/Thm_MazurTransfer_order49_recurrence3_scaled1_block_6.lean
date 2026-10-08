-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence3_scaled1_block_6
-- name    : MazurTransfer.order49_recurrence3_scaled1_block_6
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T23:48:04.59064+00:00
-- url     : https://prove2.me/theorems/c02041c1-b9c5-45ce-9ea2-d99b81176510
-- title:
--   Third order-seven recurrence: scalar1 coefficient block 6
-- statement:
--   Let $L,R$ be the exact integer coefficient lists of the two sides of the cleared first-index scalar identity in the third order-seven pseudo-division recurrence. Their block beginning at index $192$, of length at most32, agrees: $$\operatorname{take}_{32}(\operatorname{drop}_{192}(L))=\operatorname{take}_{32}(\operatorname{drop}_{192}(R)).$$ The16 blocks, together with the separately certified empty tails, reconstruct the entire original list equality.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; Apache-2.0 original attribution retained in the original parent reconstruction. Published integer model definitions retain their original values, with separate standard-axiom checked comparisons. This splits the failed full scalar1 kernel calculation into the original16 blocks of32 and an empty tail after512. Ordinary decide +kernel checks the exact coefficients; no native_decide, axioms, new hypotheses or proof-resource increases. Named downstream consumer: the exact original full scalar1_scaled_checked list identity and rational scalarResidual3Coefficient1.

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic

theorem MazurTransfer.order49_recurrence3_scaled1_block_6 : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledLeft.drop 192).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledRight.drop 192).take 32 := by sorry
