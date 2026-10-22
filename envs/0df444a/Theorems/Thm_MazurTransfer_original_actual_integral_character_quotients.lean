-- Prove2me | Theorems.Thm_MazurTransfer_original_actual_integral_character_quotients
-- name    : MazurTransfer.original_actual_integral_character_quotients
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T18:30:05.407556+00:00
-- url     : https://prove2.me/theorems/6b3e3ada-70e7-4a2e-8323-2f4b48691ab3
-- statement:
--   The previously selected pi and conjugate-pi arithmetic character maps extend as genuine finite-flat bialgebra quotients while retaining one same source Hopf model with its entire original algebra point functor, multiplication, all algebra naturality, and the previously fixed arithmetic norm-kernel labels. This holds at every original good prime and at nineteen. Every original model, map, primitive root, affine cover and field hypothesis is retained. Named downstream consumer: actual nineteen character Kummer unit conditions and original integral norm torsor pushforwards.

import Definitions.Def_MazurTransfer_OriginalActualIntegralCharacterQuotientsData20261020
import Definitions.Def_MazurTransfer_OriginalActualIntegralArithmeticKernelHopfModelsData20261020
import Theorems.Thm_MazurTransfer_original_integral_representation_quotient
import Theorems.Thm_MazurTransfer_original_actual_integral_arithmetic_kernel_hopf_models
noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13LocalIntegralCoefficientMaps MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism MazurTransfer.Order13ActualPicardSchemeNineteenNorm
open MazurTransfer.Order13ActualPicardSchemeNormGroupHom MazurTransfer.Order13GoodPrimeLocalPicardModels
open MazurTransfer.Order13GoodPrimeIntegralNormExtensions MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf
open MazurTransfer.Order13IntegralArithmeticNormKernelComparison MazurTransfer.Order13ActualPicardNormKernelGaloisAction
open MazurTransfer.Order13ActualArithmeticKernelAdditiveAction MazurTransfer.Order13ActualNormKernelF19Representation
open MazurTransfer.Order13ActualNormKernelFiniteModule MazurTransfer.Order13IntegralRepresentationQuotient
open MazurTransfer.Order13ActualIntegralArithmeticKernelHopfModels
open scoped CategoryTheory.MonObj
open MazurTransfer.NineteenRootsGaloisRepresentation MazurTransfer.Order13ActualOrderedCharacterContinuousH1
open MazurTransfer.Order13ActualIntegralCharacterQuotients
attribute [local instance] MazurTransfer.Order13ActualIntegralCharacterQuotients.instModuleZModOfNatNatAdditiveSubtypePointsMemSubgroupKernel_order13ActualIntegralCharacterQuotients
attribute [local instance] MazurTransfer.Order13ActualIntegralCharacterQuotients.instIsFiniteLeftSchemeSchemePi_order13ActualIntegralCharacterQuotients
attribute [local instance] MazurTransfer.Order13ActualIntegralCharacterQuotients.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualIntegralCharacterQuotients
attribute [local instance] MazurTransfer.Order13ActualIntegralCharacterQuotients.instFactPrimeOfNatNat_order13ActualIntegralCharacterQuotients
attribute [local instance] MazurTransfer.Order13ActualIntegralCharacterQuotients.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualIntegralCharacterQuotients
attribute [local instance] MazurTransfer.Order13ActualIntegralCharacterQuotients.instDistribMulActionAlgEquivRatAdditiveSubtypePointsMemSubgroupKernel_order13ActualIntegralCharacterQuotients
attribute [local instance] MazurTransfer.Order13ActualIntegralCharacterQuotients.instFactForallEqSubtypePointsMemSubgroupKernelSchemePiHPowOfNat_order13ActualIntegralCharacterQuotients
attribute [local instance] MazurTransfer.Order13ActualIntegralCharacterQuotients.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_order13ActualIntegralCharacterQuotients
attribute [local instance] MazurTransfer.Order13ActualIntegralCharacterQuotients.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualIntegralCharacterQuotients
attribute [local instance] MazurTransfer.Order13ActualIntegralCharacterQuotients.instFactForallEqSubtypePointsMemSubgroupKernelSchemePiConjugateHPowOfNat_order13ActualIntegralCharacterQuotients
attribute [local instance] MazurTransfer.Order13ActualIntegralCharacterQuotients.instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualIntegralCharacterQuotients
attribute [local instance] MazurTransfer.Order13ActualIntegralCharacterQuotients.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualIntegralCharacterQuotients
attribute [local instance] MazurTransfer.Order13ActualIntegralCharacterQuotients.instIsFiniteLeftSchemeSchemePiConjugate_order13ActualIntegralCharacterQuotients

theorem MazurTransfer.original_actual_integral_character_quotients : (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] {V : Type} [AddCommGroup V] [Module (ZMod 19) V] (ρ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V) (p : Representation.IntertwiningMap (kernelRepresentation K φ) ρ), ∀ (hmodel : HasArithmeticIntegralKernelHopfModel q hq K φ)
    (hp : Function.Surjective p),
HasCoherentIntegralCharacterQuotient q hq K φ ρ p) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover), HasCoherentIntegralCharacterQuotient q hq K schemePi (rootsRepresentation K)
      (piQuotient K z hz 𝒱) ∧
    HasCoherentIntegralCharacterQuotient q hq K schemePiConjugate
      (twistedRootsRepresentation K z hz) (piConjugateQuotient K z hz 𝒱)) ∧ (∀ (F : Type) [Field F] [CharZero F] [IsGalois ℚ F] [IsAlgClosed F]
    [Algebra (LocalRing 19) F] [IsScalarTower (LocalRing 19) ℚ F]
    (w : F) (hw : IsPrimitiveRoot w 13) (𝒲 : (curveScheme ℚ).TwoAffineOpenCover),
HasCoherentIntegralCharacterQuotient 19 MazurTransfer.Order13ExceptionalNineteenFlatNormFibres.nineteen_good
      F schemePi (rootsRepresentation F) (piQuotient F w hw 𝒲) ∧
    HasCoherentIntegralCharacterQuotient 19 MazurTransfer.Order13ExceptionalNineteenFlatNormFibres.nineteen_good
      F schemePiConjugate (twistedRootsRepresentation F w hw) (piConjugateQuotient F w hw 𝒲)) := by sorry
