-- Prove2me | Theorems.Thm_MazurTransfer_original_actual_integral_arithmetic_kernel_hopf_models
-- name    : MazurTransfer.original_actual_integral_arithmetic_kernel_hopf_models
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T06:41:35.888899+00:00
-- url     : https://prove2.me/theorems/1c2ba542-545c-4be2-ac40-9537992d7787
-- statement:
--   The same selected integral norms admit finite-free cocommutative Hopf models retaining the original point functor on every coefficient algebra, multiplication, all algebra-map naturality, and arithmetic labels into the previously fixed norm kernel with addition and the same existing Galois action. The labels agree with that same point functor over the original field. This holds at every original good prime and at nineteen without adding any splitting hypothesis. Named downstream consumer: actual finite-flat selected arithmetic character quotients and Kummer local conditions at nineteen.

import Definitions.Def_MazurTransfer_OriginalActualIntegralArithmeticKernelHopfModelsData20261020
import Theorems.Thm_MazurTransfer_original_integral_hopf_arithmetic_kernel_labels_laws
import Theorems.Thm_MazurTransfer_original_integral_norm_kernel_hopf_models
noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTransfer.Order13IntegralHopfArithmeticKernelLabels MazurTransfer.Order13ActualArithmeticKernelAdditiveAction
open MazurTransfer.Order13IntegralArithmeticNormKernelComparison
open MazurTransfer.Order13LocalIntegralCoefficientMaps MazurTransfer.Order13GoodPrimeLocalPicardModels
open MazurTransfer.Order13GoodPrimeIntegralNormExtensions MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison
open MazurTransfer.Order13ActualPicardSchemeNineteenNorm MazurTransfer.Order13ActualPicardSchemeNormGroupHom
open MazurTransfer.Order13ActualPicardGeometricNormPreimages MazurTransfer.Order13ActualPicardNormKummerCocycles
open MazurTransfer.Order13ActualPicardNormKernelGaloisAction MazurTransfer.Order13ExceptionalNineteenFlatNormFibres
open scoped CategoryTheory.MonObj
open MazurTransfer.Order13ActualIntegralArithmeticKernelHopfModels
attribute [local instance] MazurTransfer.Order13ActualIntegralArithmeticKernelHopfModels.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualIntegralArithmeticKernelHopfModels
attribute [local instance] MazurTransfer.Order13ActualIntegralArithmeticKernelHopfModels.instDistribMulActionAlgEquivRatAdditiveSubtypePointsMemSubgroupKernel_order13ActualIntegralArithmeticKernelHopfModels
attribute [local instance] MazurTransfer.Order13ActualIntegralArithmeticKernelHopfModels.instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualIntegralArithmeticKernelHopfModels
attribute [local instance] MazurTransfer.Order13ActualIntegralArithmeticKernelHopfModels.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualIntegralArithmeticKernelHopfModels
attribute [local instance] MazurTransfer.Order13ActualIntegralArithmeticKernelHopfModels.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualIntegralArithmeticKernelHopfModels
attribute [local instance] MazurTransfer.Order13ActualIntegralArithmeticKernelHopfModels.instFactPrimeOfNatNat_order13ActualIntegralArithmeticKernelHopfModels

theorem MazurTransfer.original_actual_integral_arithmetic_kernel_hopf_models : (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ], ∀ (hmodel : HasFiniteFreeKernelHopfModel (localLaw q hq) (integralNorm q hq φ)),
HasArithmeticIntegralKernelHopfModel q hq K φ) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K], HasArithmeticIntegralKernelHopfModel q hq K schemePi ∧
      HasArithmeticIntegralKernelHopfModel q hq K schemePiConjugate) ∧ (∀ (F : Type) [Field F] [CharZero F] [Algebra (LocalRing 19) F]
    [IsScalarTower (LocalRing 19) ℚ F],
HasArithmeticIntegralKernelHopfModel 19 nineteen_good F schemePi ∧
      HasArithmeticIntegralKernelHopfModel 19 nineteen_good F schemePiConjugate) := by sorry
