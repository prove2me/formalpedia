-- Prove2me | Theorems.Thm_MazurTransfer_original_integral_arithmetic_norm_kernel_comparison_laws
-- name    : MazurTransfer.original_integral_arithmetic_norm_kernel_comparison_laws
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T03:26:53.344091+00:00
-- url     : https://prove2.me/theorems/dd5ce07c-52de-47f4-8612-bfe8f20d2cf9
-- statement:
--   The same integral norm-kernel point equivalence preserves the original multiplication and arithmetic Galois action. It identifies points with the previously fixed kernel of the same rational norm endomorphism, with every original prime, field, scalar tower and monoid-morphism hypothesis retained. Named downstream consumer: actual finite-flat ordered arithmetic character quotients.

import Definitions.Def_MazurTransfer_OriginalIntegralArithmeticNormKernelComparisonData20261020
import Definitions.Def_MazurTransfer_OriginalRelativeNormKernelSchemePointsAndGroupLawData20261020
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormExtensionsData
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKernelGaloisActionData
import Theorems.Thm_MazurTransfer_original_integral_arithmetic_field_point_comparison_laws
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard GoodReductionJacobian NeronModelInfra
open MazurTransfer.Order13IntegralArithmeticNormKernelComparison MazurTransfer.Order13IntegralArithmeticFieldPointComparison
open MazurTransfer.Order13LocalIntegralCoefficientMaps MazurTransfer.Order13GoodPrimeLocalPicardModels
open MazurTransfer.Order13GoodPrimeIntegralNormExtensions MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison
open MazurTransfer.Order13ActualPicardGeometricNormPreimages MazurTransfer.Order13ActualPicardNormKummerCocycles
open MazurTransfer.Order13ActualPicardNormKernelGaloisAction
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13IntegralArithmeticNormKernelComparison.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralArithmeticNormKernelComparison
attribute [local instance] MazurTransfer.Order13IntegralArithmeticNormKernelComparison.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13IntegralArithmeticNormKernelComparison

theorem MazurTransfer.original_integral_arithmetic_norm_kernel_comparison_laws : (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ], ∀ (z w : Kernel K φ),
(kernelPointEquiv q hq K φ (z * w)).val =
      (localLaw q hq).mul (FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K)
        (kernelPointEquiv q hq K φ z).val (kernelPointEquiv q hq K φ w).val) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ], ∀ (σ : K ≃ₐ[ℚ] K) (z : Kernel K φ),
(kernelPointEquiv q hq K φ (σ • z)).val =
      GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom σ.toRingHom))
        (Over.w (FieldAutomorphismOverPointAction.fieldAut (LocalRing q) K (σ.restrictScalars (LocalRing q)))) (kernelPointEquiv q hq K φ z).val) := by sorry
