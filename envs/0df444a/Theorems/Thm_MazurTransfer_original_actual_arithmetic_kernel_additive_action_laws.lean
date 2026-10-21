-- Prove2me | Theorems.Thm_MazurTransfer_original_actual_arithmetic_kernel_additive_action_laws
-- name    : MazurTransfer.original_actual_arithmetic_kernel_additive_action_laws
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T03:38:16.648307+00:00
-- url     : https://prove2.me/theorems/08635233-e7e4-40ec-a1dd-d6f33a195f09
-- statement:
--   The existing arithmetic norm-kernel action on its additive type tag is exactly the same action pointwise, and under the original Galois, finite-morphism and exponent hypotheses it agrees with the previously fixed F19 representation. All original hypotheses and the same group and action providers are retained. Named downstream consumer: actual integral Hopf character quotient APIs.

import Definitions.Def_MazurTransfer_OriginalActualArithmeticKernelAdditiveActionData20261020
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison
open MazurTransfer.Order13ActualPicardNormKernelGaloisAction MazurTransfer.Order13ActualNormKernelF19Representation
open MazurTransfer.Order13ActualNormKernelFiniteModule MazurTransfer.Order13ActualArithmeticKernelAdditiveAction
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13ActualArithmeticKernelAdditiveAction.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualArithmeticKernelAdditiveAction
attribute [local instance] MazurTransfer.Order13ActualArithmeticKernelAdditiveAction.instDistribMulActionAlgEquivRatAdditiveSubtypePointsMemSubgroupKernel_order13ActualArithmeticKernelAdditiveAction
attribute [local instance] MazurTransfer.Order13ActualArithmeticKernelAdditiveAction.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualArithmeticKernelAdditiveAction
attribute [local instance] MazurTransfer.Order13ActualArithmeticKernelAdditiveAction.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualArithmeticKernelAdditiveAction

theorem MazurTransfer.original_actual_arithmetic_kernel_additive_action_laws : (∀ (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ], ∀ (σ : K ≃ₐ[ℚ] K) (z : Kernel K φ),
σ • Additive.ofMul z = Additive.ofMul (σ • z)) ∧ (∀ (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ], ∀ [IsGalois ℚ K] [IsFinite φ.left]
    [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] (σ : K ≃ₐ[ℚ] K) (z : Additive (Kernel K φ)),
σ • z = kernelRepresentation K φ σ z) := by sorry
