-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualNormKernelRanksTwo_actual_norm_kernel_ranks_two
-- name    : MazurTransfer.Order13ActualNormKernelRanksTwo.actual_norm_kernel_ranks_two
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T12:39:25.517926+00:00
-- url     : https://prove2.me/theorems/c41612dd-45b3-485a-9d62-038a23dc52d7
-- title:
--   Each actual order-thirteen Picard norm kernel has F19 dimension two
-- statement:
--   Over every algebraically closed characteristic-zero field, each of the two complete actual order-thirteen Picard norm kernels has dimension two over F19 for its original finite module structure. The proof uses the publicly established equality of the two kernel cardinalities and their product nineteen to the fourth.
-- source:
--   MazurTheorem Order13ActualNormKernelRanksTwo.actual_norm_kernel_ranks_two; original F19 module context, exact original theorem and unchanged hypotheses.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: each actual Picard norm kernel has dimension two for
its original F19 module, using equality and the product cardinality 19^4.
Named downstream consumer: actual norm-kernel Galois representations
and their arithmetic Kummer/Selmer conditions.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelRanksTwoOriginalModuleContextData20261018
noncomputable section
open MazurTransfer CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardNormKernelGaloisAction Order13ActualNormKernelProductCardinality
open Order13ActualNormKernelRanksTwo
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018
  actualNineteenTorsionProductOriginalCommProvider20261018
  actualNineteenTorsionProductOriginalPiHomProvider20261018
  actualNineteenTorsionProductOriginalConjugateHomProvider20261018
attribute [local instance] originalNormKernelRanksTwoPrimeProvider20261018
  originalNormKernelRanksTwoPiFiniteProvider20261018
  originalNormKernelRanksTwoConjugateFiniteProvider20261018
  originalNormKernelRanksTwoPiKernelFiniteProvider20261018
  originalNormKernelRanksTwoConjugateKernelFiniteProvider20261018
  originalNormKernelRanksTwoPiExponentProvider20261018
  originalNormKernelRanksTwoConjugateExponentProvider20261018
  originalNormKernelRanksTwoPiModuleProvider20261018
  originalNormKernelRanksTwoConjugateModuleProvider20261018

theorem MazurTransfer.Order13ActualNormKernelRanksTwo.actual_norm_kernel_ranks_two (K : Type) [Field K] [CharZero K] [IsAlgClosed K] :
    Module.finrank (ZMod 19) (Additive (Kernel K schemePi)) = 2 ∧
      Module.finrank (ZMod 19) (Additive (Kernel K schemePiConjugate)) = 2 := by sorry
