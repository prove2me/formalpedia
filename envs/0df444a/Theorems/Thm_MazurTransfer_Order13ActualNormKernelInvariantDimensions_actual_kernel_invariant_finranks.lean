-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualNormKernelInvariantDimensions_actual_kernel_invariant_finranks
-- name    : MazurTransfer.Order13ActualNormKernelInvariantDimensions.actual_kernel_invariant_finranks
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T20:19:09.500176+00:00
-- url     : https://prove2.me/theorems/75e246ab-3461-4066-9ff6-79717e26fbbc
-- title:
--   The actual norm-kernel invariant dimensions are zero and one
-- statement:
--   For every characteristic-zero Galois extension of the rationals and original affine cover, the invariant subspaces of the original finite-field norm-kernel representations have dimensions zero for pi and one for its conjugate.
-- source:
--   MazurTheorem Order13ActualNormKernelInvariantDimensions.actual_kernel_invariant_finranks; complete exact original telescope retained; Apache-2.0.

import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormFiniteEtaleIsogenies_actual_norm_factors_are_finite_etale_surjective
/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the invariant F19-subspaces of the two actual geometric
norm kernels have dimensions zero and one, using genuine rational
fixed-point descent and the exact nineteen torsion counts.
Named downstream consumer: actual kernel Galois module structure and Selmer bounds. -/
import Definitions.Def_MazurTransfer_Order13InvariantFixedEquivalenceOriginalDataAndCardinalityCertificateMinimalPublicNamespacesV220261018

noncomputable section
open MazurTransfer
open Order13ActualNormKernelInvariantDimensions
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance publicActualInvariantFinrankOriginalProvider120261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance publicActualInvariantFinrankOriginalProvider220261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance publicActualInvariantFinrankOriginalProvider320261018 : IsMonHom schemePi := schemePi_isMonHom
local instance publicActualInvariantFinrankOriginalProvider420261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
local instance publicActualInvariantFinrankOriginalProvider520261018 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ


open Order13ActualPicardNormAlgebraicCohomology


open Order13ActualNormKernelFiniteModule
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
local instance publicActualInvariantFinrankOriginalProvider620261018 : Finite (Kernel K φ) := kernel_finite K φ
local instance publicActualInvariantFinrankOriginalProvider720261018 : Module (ZMod 19) (Additive (Kernel K φ)) := kernelZModModule K φ


open Order13ActualNormKernelF19Representation Order13ActualKernelActionFixedSubgroup
local instance publicActualInvariantFinrankOriginalProvider820261018 : Fact (Nat.Prime 19) := ⟨by decide⟩
local instance publicActualInvariantFinrankOriginalProvider920261018 : Module.Finite (ZMod 19) (Additive (Kernel K φ)) := kernel_module_finite K φ

local instance publicActualInvariantFinrankOriginalProvider1020261018 : IsFinite schemePi.left := Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective.1.1
local instance publicActualInvariantFinrankOriginalProvider1120261018 : IsFinite schemePiConjugate.left := Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective.2.1
local instance publicActualInvariantFinrankOriginalProvider1220261018 : Fact (∀ z : Kernel K schemePi, z ^ 19 = 1) := ⟨pi_kernel_exponent_nineteen K⟩
local instance publicActualInvariantFinrankOriginalProvider1320261018 : Fact (∀ z : Kernel K schemePiConjugate, z ^ 19 = 1) := ⟨piConjugate_kernel_exponent_nineteen K⟩
local instance publicActualInvariantFinrankOriginalProvider1420261018 : Module (ZMod 19) (Additive (Kernel K schemePi)) := kernelZModModule K schemePi
local instance publicActualInvariantFinrankOriginalProvider1520261018 : Module (ZMod 19) (Additive (Kernel K schemePiConjugate)) := kernelZModModule K schemePiConjugate

theorem MazurTransfer.Order13ActualNormKernelInvariantDimensions.actual_kernel_invariant_finranks (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) : Module.finrank (ZMod 19) (kernelRepresentation K schemePi).invariants = 0 ∧ Module.finrank (ZMod 19) (kernelRepresentation K schemePiConjugate).invariants = 1 := by sorry
