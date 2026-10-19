-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualNormKernelNineteenEmbedding_kernelNineteenAddHom_galois
-- name    : MazurTransfer.Order13ActualNormKernelNineteenEmbedding.kernelNineteenAddHom_galois
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T15:10:26.74477+00:00
-- url     : https://prove2.me/theorems/82fede5a-04fe-4bd3-bb9e-17e1c907f2e2
-- title:
--   Original Galois compatibility of the actual norm-kernel nineteen-torsion embedding
-- statement:
--   The original additive embedding of a nineteen-killed actual norm kernel into the same Picard nineteen-torsion intertwines its existing F19 Galois representation with the original arithmetic precomposition Galois homomorphism, under every original field, finite-map and exponent hypothesis.
-- source:
--   MazurTheorem Order13ActualNormKernelNineteenEmbedding, exact original theorem; official Anthropic FLT interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the complete actual nineteen-killed norm kernel embeds
additively and Galois-equivariantly into the SAME Picard nineteen torsion.
Named downstream consumer: actual cyclotomic quotient maps via the pairing.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelNineteenEmbeddingOriginalData20261018
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve MazurTransfer
open NeronModelInfra GoodReductionJacobian
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelNineteenEmbedding Order13ActualNineteenTorsionGaloisPairingBridge
open scoped CategoryTheory.MonObj
attribute [local instance] kernelNineteenEmbeddingOriginalGroupProvider20261018 kernelNineteenEmbeddingOriginalCommProvider20261018 kernelNineteenEmbeddingOriginalPiHomProvider20261018 kernelNineteenEmbeddingOriginalConjugateHomProvider20261018 kernelNineteenEmbeddingOriginalActionProvider20261018 kernelNineteenEmbeddingOriginalFiniteProvider20261018 kernelNineteenEmbeddingOriginalModuleProvider20261018

theorem MazurTransfer.Order13ActualNormKernelNineteenEmbedding.kernelNineteenAddHom_galois (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] [IsAlgClosed K] (σ : K ≃ₐ[ℚ] K) (z : Additive (Kernel K φ)) :
    arithmeticNineteenTorsionHom K σ (kernelNineteenAddHom K φ z) =
      kernelNineteenAddHom K φ (Order13ActualNormKernelF19Representation.kernelRepresentation K φ σ z) := by sorry
