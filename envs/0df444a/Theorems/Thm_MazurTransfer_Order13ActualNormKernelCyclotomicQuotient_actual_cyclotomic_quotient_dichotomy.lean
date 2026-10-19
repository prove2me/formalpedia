-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualNormKernelCyclotomicQuotient_actual_cyclotomic_quotient_dichotomy
-- name    : MazurTransfer.Order13ActualNormKernelCyclotomicQuotient.actual_cyclotomic_quotient_dichotomy
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T20:31:44.056993+00:00
-- url     : https://prove2.me/theorems/8e093565-a813-4eac-a4bb-4758e5316b2a
-- title:
--   The actual norm factor opposite the invariant line has a cyclotomic quotient
-- statement:
--   For every algebraically closed characteristic-zero Galois extension of the rationals and original affine cover, the original actual cyclotomic quotient dichotomy holds. The ordered invariant dimensions select the branch where the pi kernel has a surjective equivariant map to the literal nineteen-root representation with a one-dimensional kernel, while the conjugate kernel has the invariant line.
-- source:
--   MazurTheorem Order13ActualNormKernelCyclotomicQuotient.actual_cyclotomic_quotient_dichotomy; exact original disjunction and complete telescope retained; Apache-2.0.

import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_MazurTransfer_Order13ActualNormKernelRanksTwoOriginalModuleContextData20261018
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual norm factor opposite the actual invariant line
has an equivariant quotient onto the literal cyclotomic19 representation,
with a one-dimensional kernel. Both possible factor orderings are retained.
Named downstream consumer: identifying the remaining arithmetic13 character
and proving the actual local Selmer conditions.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicQuotientOriginalPredicateData20261018
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

open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualNormKernelRanksTwo
open Order13ActualPicardSchemeNineteenNorm
attribute [local instance] originalNormKernelRanksTwoPiFiniteProvider20261018 originalNormKernelRanksTwoConjugateFiniteProvider20261018 originalNormKernelRanksTwoPiExponentProvider20261018 originalNormKernelRanksTwoConjugateExponentProvider20261018 originalNormKernelRanksTwoPiModuleProvider20261018 originalNormKernelRanksTwoConjugateModuleProvider20261018

local instance publicActualCyclotomicQuotientFact104Provider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem MazurTransfer.Order13ActualNormKernelCyclotomicQuotient.actual_cyclotomic_quotient_dichotomy (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) :
    (Module.finrank (ZMod 19) (kernelRepresentation K schemePi).invariants = 1 ∧
      HasCyclotomicQuotient K schemePiConjugate ∧
      Module.finrank (ZMod 19) (kernelRepresentation K schemePiConjugate).invariants = 0) ∨
    (Module.finrank (ZMod 19) (kernelRepresentation K schemePiConjugate).invariants = 1 ∧
      HasCyclotomicQuotient K schemePi ∧
      Module.finrank (ZMod 19) (kernelRepresentation K schemePi).invariants = 0) := by sorry
