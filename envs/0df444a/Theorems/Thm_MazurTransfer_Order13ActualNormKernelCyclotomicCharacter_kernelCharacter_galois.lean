-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualNormKernelCyclotomicCharacter_kernelCharacter_galois
-- name    : MazurTransfer.Order13ActualNormKernelCyclotomicCharacter.kernelCharacter_galois
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T15:34:05.997194+00:00
-- url     : https://prove2.me/theorems/2351a0a2-d064-460f-b441-96c8e4217741
-- title:
--   Arithmetic Galois equivariance of the actual norm-kernel pairing character
-- statement:
--   Pairing against an actual norm-kernel vector fixed by its existing F19 Galois representation gives an equivariant character of the other actual norm kernel into the literal nineteen-th roots of unity. Every original field, finite-map, exponent and fixed-vector hypothesis is retained.
-- source:
--   MazurTheorem Order13ActualNormKernelCyclotomicCharacter, exact original theorem; official Anthropic FLT interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: pairing against an actual fixed norm-kernel vector gives
an equivariant character of the other actual norm kernel into literal roots
of unity. Named downstream consumer: the actual cyclotomic quotient dichotomy.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicCharacterOriginalData20261018
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelNineteenEmbedding_kernelNineteenAddHom_galois
import Theorems.Thm_MazurTransfer_Order13ActualNineteenPairingGaloisCovariance_actualPairing_galois
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve MazurTransfer
open GoodReductionJacobian NeronModelInfra
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelNineteenEmbedding Order13ActualNormKernelF19Representation
open Order13ActualNineteenTorsionGaloisPairingBridge Order13ActualGeometricNineteenDivisorialPairing
open Order13ActualNineteenPairingGaloisCovariance Order13ActualNormKernelCyclotomicCharacter
open NineteenRootsGaloisRepresentation
open scoped CategoryTheory.MonObj
attribute [local instance] kernelCharacterOriginalGroupProvider20261018 kernelCharacterOriginalCommProvider20261018 kernelCharacterOriginalPiHomProvider20261018 kernelCharacterOriginalConjugateHomProvider20261018 kernelCharacterOriginalPrimeProvider20261018 kernelCharacterOriginalLeftModuleProvider20261018 kernelCharacterOriginalRightModuleProvider20261018 kernelCharacterOriginalRootsModuleProvider20261018

theorem MazurTransfer.Order13ActualNormKernelCyclotomicCharacter.kernelCharacter_galois (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (φ ψ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    [IsMonHom φ] [IsMonHom ψ] [IsFinite φ.left] [IsFinite ψ.left]
    [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] [Fact (∀ z : Kernel K ψ, z ^ 19 = 1)] (a : Additive (Kernel K φ))
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K φ σ a = a)
    (σ : K ≃ₐ[ℚ] K) (z : Additive (Kernel K ψ)) :
    kernelCharacterLinear K φ ψ a (kernelRepresentation K ψ σ z) =
      rootsRepresentation K σ (kernelCharacterLinear K φ ψ a z) := by sorry
