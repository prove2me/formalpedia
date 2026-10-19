-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualNormKernelCyclotomicQuotient_hasCyclotomicQuotient_of_fixed_line
-- name    : MazurTransfer.Order13ActualNormKernelCyclotomicQuotient.hasCyclotomicQuotient_of_fixed_line
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T16:23:48.555172+00:00
-- url     : https://prove2.me/theorems/39c17ef8-2d84-4c80-aa98-24ebc65db271
-- title:
--   An actual fixed norm-kernel line gives a cyclotomic quotient
-- statement:
--   Let K be an algebraically closed Galois extension of the rationals and let φ and ψ be finite actual Picard norm endomorphisms whose kernels have exponent 19. Assume their cross pairing is left nondegenerate, the φ-kernel representation has a one-dimensional fixed subspace, and the ψ-kernel has dimension two over the field with 19 elements. Then the ψ-kernel representation has a surjective equivariant map to the literal nineteenth roots of unity with a one-dimensional kernel.
-- source:
--   MazurTheorem Order13ActualNormKernelCyclotomicQuotient.hasCyclotomicQuotient_of_fixed_line; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual norm factor opposite the actual invariant line
has an equivariant quotient onto the literal cyclotomic19 representation,
with a one-dimensional kernel. Both possible factor orderings are retained.
Named downstream consumer: identifying the remaining arithmetic13 character
and proving the actual local Selmer conditions.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicQuotientOriginalPredicateData20261018
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelCyclotomicCharacter_kernelCharacterLinear_surjective_of_cross
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve MazurTransfer
open NeronModelInfra GoodReductionJacobian
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelCyclotomicCharacter Order13ActualNormKernelCyclotomicQuotient
open Order13ActualNormKernelF19Representation NineteenRootsGaloisRepresentation
open Order13ActualNineteenTorsionNormPairingAdjoint Order13ActualNormKernelProductCardinality
open Order13ActualNormKernelNineteenEmbedding
open scoped CategoryTheory.MonObj
attribute [local instance] kernelCharacterOriginalGroupProvider20261018 kernelCharacterOriginalCommProvider20261018 kernelCharacterOriginalPiHomProvider20261018 kernelCharacterOriginalConjugateHomProvider20261018 kernelCharacterOriginalPrimeProvider20261018 kernelCharacterOriginalLeftModuleProvider20261018 kernelCharacterOriginalRightModuleProvider20261018 kernelCharacterOriginalRootsModuleProvider20261018 kernelNineteenEmbeddingOriginalFiniteProvider20261018

theorem MazurTransfer.Order13ActualNormKernelCyclotomicQuotient.hasCyclotomicQuotient_of_fixed_line (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (φ ψ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    [IsMonHom φ] [IsMonHom ψ] [IsFinite φ.left] [IsFinite ψ.left]
    [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] [Fact (∀ z : Kernel K ψ, z ^ 19 = 1)]
    (hcross : ∀ x : (actualNineteenTorsionNormHom K φ).ker,
      (∀ y : (actualNineteenTorsionNormHom K ψ).ker,
        Order13ActualGeometricNineteenDivisorialPairing.actualGeometricNineteenPairing K x.val y.val = 1) → x = 0)
    (hI : Module.finrank (ZMod 19) (kernelRepresentation K φ).invariants = 1)
    (hV : Module.finrank (ZMod 19) (Additive (Kernel K ψ)) = 2) :
    HasCyclotomicQuotient K ψ := by sorry
