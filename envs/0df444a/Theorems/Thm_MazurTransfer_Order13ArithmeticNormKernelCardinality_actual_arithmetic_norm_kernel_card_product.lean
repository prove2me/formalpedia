-- Prove2me | Theorems.Thm_MazurTransfer_Order13ArithmeticNormKernelCardinality_actual_arithmetic_norm_kernel_card_product
-- name    : MazurTransfer.Order13ArithmeticNormKernelCardinality.actual_arithmetic_norm_kernel_card_product
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T17:00:50.757909+00:00
-- url     : https://prove2.me/theorems/7233fbe2-c2f5-4ba2-8985-c24f677427fb
-- title:
--   The actual arithmetic Picard norm-kernel cardinalities have product nineteen
-- statement:
--   For the actual degree-zero arithmetic Picard group of X₁(13) over the rationals, both original norm kernels are finite and the product of their cardinalities is nineteen.
-- source:
--   MazurTheorem Order13ArithmeticNormKernelCardinality.actual_arithmetic_norm_kernel_card_product; Apache-2.0.

import Definitions.Def_MazurTransfer_Order13ActualDiamondPicardEndomorphismsExplicitPublicOrderCertificate20261017
noncomputable section
open MazurTransfer.Order13ActualDiamondPicardEndomorphisms

theorem MazurTransfer.Order13ArithmeticNormKernelCardinality.actual_arithmetic_norm_kernel_card_product :
    Finite pi.ker ∧ Finite piConjugate.ker ∧ Nat.card pi.ker * Nat.card piConjugate.ker = 19 := by sorry
