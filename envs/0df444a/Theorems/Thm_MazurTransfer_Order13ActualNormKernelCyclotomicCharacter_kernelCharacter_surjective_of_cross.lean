-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualNormKernelCyclotomicCharacter_kernelCharacter_surjective_of_cross
-- name    : MazurTransfer.Order13ActualNormKernelCyclotomicCharacter.kernelCharacter_surjective_of_cross
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T15:39:18.207304+00:00
-- url     : https://prove2.me/theorems/515385fc-81f1-4c10-8612-3f786f6d31c1
-- title:
--   Original surjectivity of the actual norm-kernel character from a nondegenerate cross pairing
-- statement:
--   The original actual pairing character from one norm kernel to nineteen-th roots is surjective when the supplied cross pairing is nondegenerate on the first norm kernel and the chosen vector there is nonzero. Every original finite-map, exponent and field hypothesis is retained.
-- source:
--   MazurTheorem Order13ActualNormKernelCyclotomicCharacter, exact original theorem, using the proved prime-roots character surjectivity API.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: pairing against an actual fixed norm-kernel vector gives
an equivariant character of the other actual norm kernel into literal roots
of unity. Named downstream consumer: the actual cyclotomic quotient dichotomy.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicCharacterOriginalData20261018
import Theorems.Thm_MazurTransfer_prime_roots_character_surjective
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve MazurTransfer
open GoodReductionJacobian NeronModelInfra
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelNineteenEmbedding Order13ActualNormKernelF19Representation
open Order13ActualNormKernelProductCardinality Order13ActualNineteenTorsionNormPairingAdjoint
open Order13ActualPicardNormKummerCocycles
open Order13ActualNineteenTorsionGaloisPairingBridge Order13ActualGeometricNineteenDivisorialPairing
open Order13ActualNormKernelCyclotomicCharacter
open NineteenRootsGaloisRepresentation
open scoped CategoryTheory.MonObj
attribute [local instance] kernelCharacterOriginalGroupProvider20261018 kernelCharacterOriginalCommProvider20261018 kernelCharacterOriginalPiHomProvider20261018 kernelCharacterOriginalConjugateHomProvider20261018 kernelCharacterOriginalPrimeProvider20261018 kernelCharacterOriginalLeftModuleProvider20261018 kernelCharacterOriginalRightModuleProvider20261018 kernelCharacterOriginalRootsModuleProvider20261018

theorem MazurTransfer.Order13ActualNormKernelCyclotomicCharacter.kernelCharacter_surjective_of_cross (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (φ ψ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    [IsMonHom φ] [IsMonHom ψ] [IsFinite φ.left] [IsFinite ψ.left]
    [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] [Fact (∀ z : Kernel K ψ, z ^ 19 = 1)]
    (hcross : ∀ x : (actualNineteenTorsionNormHom K φ).ker,
      (∀ y : (actualNineteenTorsionNormHom K ψ).ker,
        actualGeometricNineteenPairing K x.val y.val = 1) → x = 0)
    (a : Additive (Kernel K φ)) (ha : a ≠ 0) :
    Function.Surjective (kernelCharacter K φ ψ a) := by sorry
