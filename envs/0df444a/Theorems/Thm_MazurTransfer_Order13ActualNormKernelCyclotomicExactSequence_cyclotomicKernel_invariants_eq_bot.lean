-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualNormKernelCyclotomicExactSequence_cyclotomicKernel_invariants_eq_bot
-- name    : MazurTransfer.Order13ActualNormKernelCyclotomicExactSequence.cyclotomicKernel_invariants_eq_bot
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T21:00:55.593486+00:00
-- url     : https://prove2.me/theorems/55097385-3ad7-4567-b25e-707b24785750
-- title:
--   The cyclotomic kernel representation inherits vanishing ambient invariants
-- statement:
--   For the original character-kernel representation inside an actual geometric norm-kernel representation, vanishing invariants of the ambient representation imply vanishing invariants of the kernel representation.
-- source:
--   MazurTheorem Order13ActualNormKernelCyclotomicExactSequence.cyclotomicKernel_invariants_eq_bot; exact complete original telescope and hypothesis retained; Apache-2.0.

import Definitions.Def_MazurTransfer_Order13CyclotomicKernelExactSequenceOriginalDataAndStructuralCertificates20261018
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the kernel representation has no invariants when its ambient actual norm-kernel representation has none. Named downstream consumer: Order13ActualArithmeticCharacterExactSequence.actual_arithmetic_character_exact_sequence_dichotomy.
-/
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

open Order13ActualNormKernelCyclotomicExactSequence

theorem MazurTransfer.Order13ActualNormKernelCyclotomicExactSequence.cyclotomicKernel_invariants_eq_bot (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (ψ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    [IsMonHom ψ] [IsFinite ψ.left] [Fact (∀ z : Kernel K ψ, z ^ 19 = 1)]
    (f : Representation.IntertwiningMap (kernelRepresentation K ψ) (rootsRepresentation K))
    (hV : (kernelRepresentation K ψ).invariants = ⊥) :
    (cyclotomicKernelRepresentation K ψ f).invariants = ⊥ := by sorry
