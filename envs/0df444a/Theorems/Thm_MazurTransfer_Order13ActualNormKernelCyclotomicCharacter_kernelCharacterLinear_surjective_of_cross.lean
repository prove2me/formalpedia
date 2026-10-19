-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualNormKernelCyclotomicCharacter_kernelCharacterLinear_surjective_of_cross
-- name    : MazurTransfer.Order13ActualNormKernelCyclotomicCharacter.kernelCharacterLinear_surjective_of_cross
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T15:59:26.417666+00:00
-- url     : https://prove2.me/theorems/976aa320-fc7d-45b2-b8a7-5bb2dcf7ab3c
-- title:
--   Original F19-linear surjectivity of the actual norm-kernel pairing character
-- statement:
--   Under the original supplied cross-pairing nondegeneracy and nonzero-vector hypotheses, the original F19-linear actual norm-kernel character onto the additive group of literal nineteen-th roots is surjective. Every original field, finite-map and exponent hypothesis is retained.
-- source:
--   MazurTheorem Order13ActualNormKernelCyclotomicCharacter.kernelCharacterLinear_surjective_of_cross, exact original theorem.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: pairing against an actual fixed norm-kernel vector gives
an equivariant character of the other actual norm kernel into literal roots
of unity. Named downstream consumer: the actual cyclotomic quotient dichotomy.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicCharacterOriginalData20261018
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelCyclotomicCharacter_kernelCharacter_surjective_of_cross
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

theorem MazurTransfer.Order13ActualNormKernelCyclotomicCharacter.kernelCharacterLinear_surjective_of_cross (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (φ ψ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    [IsMonHom φ] [IsMonHom ψ] [IsFinite φ.left] [IsFinite ψ.left]
    [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] [Fact (∀ z : Kernel K ψ, z ^ 19 = 1)]
    (hcross : ∀ x : (actualNineteenTorsionNormHom K φ).ker,
      (∀ y : (actualNineteenTorsionNormHom K ψ).ker,
        actualGeometricNineteenPairing K x.val y.val = 1) → x = 0)
    (a : Additive (Kernel K φ)) (ha : a ≠ 0) :
    Function.Surjective (kernelCharacterLinear K φ ψ a) := by sorry
