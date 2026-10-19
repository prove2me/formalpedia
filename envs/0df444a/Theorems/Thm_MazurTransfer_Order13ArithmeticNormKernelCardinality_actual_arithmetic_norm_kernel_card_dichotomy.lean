-- Prove2me | Theorems.Thm_MazurTransfer_Order13ArithmeticNormKernelCardinality_actual_arithmetic_norm_kernel_card_dichotomy
-- name    : MazurTransfer.Order13ArithmeticNormKernelCardinality.actual_arithmetic_norm_kernel_card_dichotomy
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T18:08:20.519847+00:00
-- url     : https://prove2.me/theorems/892e7864-103c-4c02-a91f-712a8fcd03f4
-- title:
--   The arithmetic norm kernels have orders nineteen and one in some order
-- statement:
--   The two actual arithmetic Picard norm kernels have cardinalities nineteen and one, in one of the two possible orders. This is the original cardinality dichotomy for the actual complementary norm endomorphisms of the X₁(13) function-field Picard group over the rationals.
-- source:
--   MazurTheorem Order13ArithmeticNormKernelCardinality.actual_arithmetic_norm_kernel_card_dichotomy; official Anthropic FLT arithmetic Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0.

import Definitions.Def_MazurTransfer_Order13ActualDiamondPicardEndomorphismsExplicitPublicOrderCertificate20261017
noncomputable section
open MazurTransfer.Order13ActualDiamondPicardEndomorphisms

theorem MazurTransfer.Order13ArithmeticNormKernelCardinality.actual_arithmetic_norm_kernel_card_dichotomy :
    (Nat.card pi.ker = 19 ∧ Nat.card piConjugate.ker = 1) ∨
      (Nat.card pi.ker = 1 ∧ Nat.card piConjugate.ker = 19) := by sorry
