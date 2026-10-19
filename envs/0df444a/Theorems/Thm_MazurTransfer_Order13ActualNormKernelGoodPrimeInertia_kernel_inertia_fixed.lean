-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualNormKernelGoodPrimeInertia_kernel_inertia_fixed
-- name    : MazurTransfer.Order13ActualNormKernelGoodPrimeInertia.kernel_inertia_fixed
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T01:21:59.917685+00:00
-- url     : https://prove2.me/theorems/dc2fb314-d3d8-4977-b05c-8377c196c9c1
-- statement:
--   Valuation inertia at every prime outside two, thirteen and nineteen acts trivially on both actual geometric norm kernels. This uses the original norm maps, valuation inertia subgroup and kernel action, with no geometric-degree assumption. The downstream consumer is the local character Kummer lift argument.

import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKummerData
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormExtensionsData
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKernelGaloisActionData
import Theorems.Thm_MazurTransfer_Order13GoodPrimeUnramifiedKummer_norm_lift_inertia_fixed
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardNormKummerCocycles
open Order13LocalIntegralCoefficientMaps
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison.actualGroup
attribute [local instance] MazurTransfer.Order13ActualPicardNormKummerCocycles.actualPicardNormKummerDataProvider220261017


open Order13ActualPicardNormKernelGaloisAction
local instance publicGoodPrimeKernelActionProvider20261019 (K : Type) [Field K] [CharZero K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] :
    MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ

theorem MazurTransfer.Order13ActualNormKernelGoodPrimeInertia.kernel_inertia_fixed (K : Type) [Field K] [CharZero K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19)
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring K) (hA : A.LiesOverPrime q)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (z : Kernel K φ) :
    σ • z = z := by sorry
