-- Prove2me | Theorems.Thm_MazurTransfer_original_integral_hopf_arithmetic_kernel_labels_laws
-- name    : MazurTransfer.original_integral_hopf_arithmetic_kernel_labels_laws
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T04:28:26.024811+00:00
-- url     : https://prove2.me/theorems/5359e7c0-5573-4cec-b0f9-f8488372fec4
-- statement:
--   The original point labels from the same integral Hopf algebra into the previously fixed arithmetic norm kernel preserve multiplication and spectrum-precomposition arithmetic Galois action under exactly the original multiplication and naturality hypotheses. The additive labels preserve addition and the same fixed additive action. All original prime, field, coefficient tower, Hopf algebra, endomorphism and labeling hypotheses are retained. Named downstream consumer: actual finite-flat ordered arithmetic character quotients.

import Definitions.Def_MazurTransfer_OriginalIntegralHopfArithmeticKernelLabelsData20261020
import Theorems.Thm_MazurTransfer_original_integral_arithmetic_norm_kernel_comparison_laws
noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTransfer.Order13IntegralArithmeticNormKernelComparison MazurTransfer.Order13IntegralArithmeticFieldPointComparison
open MazurTransfer.Order13LocalIntegralCoefficientMaps MazurTransfer.Order13GoodPrimeLocalPicardModels
open MazurTransfer.Order13GoodPrimeIntegralNormExtensions MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison
open MazurTransfer.Order13ActualPicardGeometricNormPreimages MazurTransfer.Order13ActualPicardNormKummerCocycles
open MazurTransfer.Order13ActualPicardNormKernelGaloisAction MazurTransfer.Order13ActualArithmeticKernelAdditiveAction
open scoped CategoryTheory.MonObj
open MazurTransfer.Order13IntegralHopfArithmeticKernelLabels
attribute [local instance] MazurTransfer.Order13IntegralHopfArithmeticKernelLabels.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralHopfArithmeticKernelLabels
attribute [local instance] MazurTransfer.Order13IntegralHopfArithmeticKernelLabels.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13IntegralHopfArithmeticKernelLabels
attribute [local instance] MazurTransfer.Order13IntegralHopfArithmeticKernelLabels.instDistribMulActionAlgEquivRatAdditiveSubtypePointsMemSubgroupKernel_order13IntegralHopfArithmeticKernelLabels

theorem MazurTransfer.original_integral_hopf_arithmetic_kernel_labels_laws : (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] {H : Type} [CommRing H] [HopfAlgebra (LocalRing q) H] (e : WithConv (H →ₐ[LocalRing q] K) ≃ kernelPoints (localLaw q hq) (integralNorm q hq φ) (MazurTransfer.FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K)), ∀ (hMul : ∀ f g, (e (f * g)).val = (localLaw q hq).mul _ (e f).val (e g).val)
    (f g : WithConv (H →ₐ[LocalRing q] K)),
fixedKernelLabel q hq K φ e (f * g) =
      fixedKernelLabel q hq K φ e f * fixedKernelLabel q hq K φ e g) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] {H : Type} [CommRing H] [HopfAlgebra (LocalRing q) H] (e : WithConv (H →ₐ[LocalRing q] K) ≃ kernelPoints (localLaw q hq) (integralNorm q hq φ) (MazurTransfer.FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K)), ∀ (σ : K ≃ₐ[ℚ] K)
    (f g : WithConv (H →ₐ[LocalRing q] K))
    (hNat : (e g).val.val = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (e f).val.val),
fixedKernelLabel q hq K φ e g = σ • fixedKernelLabel q hq K φ e f) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] {H : Type} [CommRing H] [HopfAlgebra (LocalRing q) H] (e : WithConv (H →ₐ[LocalRing q] K) ≃ kernelPoints (localLaw q hq) (integralNorm q hq φ) (MazurTransfer.FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K)), ∀ (hMul : ∀ f g, (e (f * g)).val = (localLaw q hq).mul _ (e f).val (e g).val)
    (f g : WithConv (H →ₐ[LocalRing q] K)),
arithmeticKernelLabel q hq K φ e (f * g) =
      arithmeticKernelLabel q hq K φ e f + arithmeticKernelLabel q hq K φ e g) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] {H : Type} [CommRing H] [HopfAlgebra (LocalRing q) H] (e : WithConv (H →ₐ[LocalRing q] K) ≃ kernelPoints (localLaw q hq) (integralNorm q hq φ) (MazurTransfer.FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K)), ∀ (σ : K ≃ₐ[ℚ] K)
    (f g : WithConv (H →ₐ[LocalRing q] K))
    (hNat : (e g).val.val = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (e f).val.val),
arithmeticKernelLabel q hq K φ e g = σ • arithmeticKernelLabel q hq K φ e f) := by sorry
