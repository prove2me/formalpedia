-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualNormKernelEigenCharacterQuotient_kernelEigenCharacterIntertwining_surjective
-- name    : MazurTransfer.Order13ActualNormKernelEigenCharacterQuotient.kernelEigenCharacterIntertwining_surjective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T00:27:03.214012+00:00
-- url     : https://prove2.me/theorems/89089c3a-255d-4dfe-9868-bb9e851e905f
-- statement:
--   The original pairing quotient against a nonzero actual character eigenvector is surjective whenever the same actual norm-kernel cross-pairing is nondegenerate. The full original generic norm maps, finiteness, exponent, eigenvector, and nonzero hypotheses are retained.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNormKernelEigenCharacterIntertwiningOriginalDataAndEquivarianceCertificate20261018
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelCyclotomicCharacter_kernelCharacterLinear_surjective_of_cross
noncomputable section
open MazurTransfer
open Order13ActualNormKernelEigenCharacterQuotient
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
open Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelCyclotomicCharacter Order13ActualNormKernelFiniteModule
open Order13ActualNormKernelNineteenEmbedding Order13ActualNormKernelF19Representation
open NineteenRootsGaloisRepresentation Order13ActualNineteenTorsionNormPairingAdjoint
open Order13ActualGeometricNineteenDivisorialPairing
attribute [local instance] kernelCharacterOriginalGroupProvider20261018 kernelCharacterOriginalCommProvider20261018 kernelCharacterOriginalPiHomProvider20261018 kernelCharacterOriginalConjugateHomProvider20261018 kernelCharacterOriginalPrimeProvider20261018 kernelCharacterOriginalLeftModuleProvider20261018 kernelCharacterOriginalRightModuleProvider20261018 kernelCharacterOriginalRootsModuleProvider20261018
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
variable (φ ψ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
  [IsMonHom φ] [IsMonHom ψ] [IsFinite φ.left] [IsFinite ψ.left]
  [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] [Fact (∀ z : Kernel K ψ, z ^ 19 = 1)]

theorem MazurTransfer.Order13ActualNormKernelEigenCharacterQuotient.kernelEigenCharacterIntertwining_surjective
    (hcross : ∀ x : (actualNineteenTorsionNormHom K φ).ker,
      (∀ y : (actualNineteenTorsionNormHom K ψ).ker,
        actualGeometricNineteenPairing K x.val y.val = 1) → x = 0)
    (χ : (K ≃ₐ[ℚ] K) →* (ZMod 19)ˣ) (b : Additive (Kernel K φ)) (hb0 : b ≠ 0)
    (hb : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K φ σ b = (χ σ : ZMod 19) • b) :
    Function.Surjective (kernelEigenCharacterIntertwining K φ ψ χ b hb) := by sorry
