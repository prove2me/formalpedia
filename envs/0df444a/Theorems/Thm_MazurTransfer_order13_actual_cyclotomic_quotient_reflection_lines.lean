-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_cyclotomic_quotient_reflection_lines
-- name    : MazurTransfer.order13_actual_cyclotomic_quotient_reflection_lines
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T22:40:34.489912+00:00
-- url     : https://prove2.me/theorems/9af3589c-e0b2-4a13-8948-02e3584a4444
-- title:
--   Both actual cyclotomic character kernels are their reflected-vector lines
-- statement:
--   Over an algebraically closed Galois field $K/\mathbb Q$ of characteristic zero, let $r$ be an original reflection parameter and $a$ a nonzero vector in either complete actual norm kernel. The kernel of its original pairing character on the opposite norm kernel is exactly
--   \[\ker(\chi_a)=\operatorname{span}_{\mathbb F_{19}}\{R_r a\}.\]
--   Both norm-factor orderings retain their separate exact original universal statements. The statement uses the same represented kernels and the same actual divisorial pairing.
-- source:
--   MazurTheorem Order13ActualCyclotomicQuotientReflectionLine.pi_character_kernel_eq_reflection_line and piConjugate_character_kernel_eq_reflection_line; conjunction of the two exact complete original closed propositions, with both original reflection-membership helper propositions; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNormKernelReflectionOriginalRestrictedCompleteEquivalencesAndEmbeddingCertificatesExplicitFiniteExponentContextV220261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelRanksTwoOriginalModuleContextData20261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicQuotientOriginalPredicateData20261018
import Theorems.Thm_MazurTransfer_order13_actual_pairing_self_reflection
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelCyclotomicCharacter_kernelCharacterLinear_surjective_of_cross
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelCrossPairing_pi_cross_left_nondegenerate
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelCrossPairing_piConjugate_cross_left_nondegenerate
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelRanksTwo_actual_norm_kernel_ranks_two
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

local instance publicReflectionLineRationalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

open Order13ReflectionParameter Order13ActualNormKernelReflection
open Order13ActualReflectionPairingOrthogonality Order13ActualGeometricNineteenDivisorialPairing

theorem MazurTransfer.order13_actual_cyclotomic_quotient_reflection_lines :
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (r : ReflectionParameter K)
    (a : Additive (Kernel K schemePi)) (ha : a ≠ 0),
    LinearMap.ker (kernelCharacterLinear K schemePi schemePiConjugate a) =
      Submodule.span (ZMod 19) {piKernelReflection K r a}) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (r : ReflectionParameter K)
    (a : Additive (Kernel K schemePiConjugate)) (ha : a ≠ 0),
    LinearMap.ker (kernelCharacterLinear K schemePiConjugate schemePi a) =
      Submodule.span (ZMod 19) {piConjugateKernelReflection K r a}) := by sorry
