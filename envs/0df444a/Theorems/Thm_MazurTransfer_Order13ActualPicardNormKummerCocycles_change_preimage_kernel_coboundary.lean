-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardNormKummerCocycles_change_preimage_kernel_coboundary
-- name    : MazurTransfer.Order13ActualPicardNormKummerCocycles.change_preimage_kernel_coboundary
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T22:03:18.717656+00:00
-- url     : https://prove2.me/theorems/433711b7-67ba-4241-a16b-e723e9570d33
-- title:
--   Changing an actual norm preimage changes its Kummer difference by a kernel coboundary
-- statement:
--   Let P be the same rational represented Picard group scheme, K a characteristic-zero field, and phi an internal monoid endomorphism of P. Let a be a rational point and let b,b prime in P(K) both map to its scalar extension under phi. Set z=b prime times b inverse and c_b(sigma)=sigma(b)b inverse. Then z lies in the kernel and, for every Q-automorphism sigma of K, $$\varphi(z)=1,\qquad c_{b\prime}(\sigma)=\sigma(z)c_b(\sigma)z^{-1}.$$ Thus the Kummer cocycle class is independent of the chosen preimage. The named downstream consumers are actual norm Kummer classes and the norm Selmer descent.
-- source:
--   Complete original MazurTheorem Order13ActualPicardNormKummerCocycles.change_preimage_kernel_coboundary statement and main proof, with two complete original generic helper types compared separately. Same actual Picard and original five Kummer constructors, all fully compared with their original types and values. Official Anthropic FLT Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

import Definitions.Def_MazurTransfer_Order13ActualPicardNormKummerData
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open scoped CategoryTheory.MonObj
local instance publicChangePreimageKummerStatementProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance publicChangePreimageKummerStatementProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance publicChangePreimageKummerStatementProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance publicChangePreimageKummerStatementProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open MazurTransfer.Order13ActualPicardNormKummerCocycles

theorem MazurTransfer.Order13ActualPicardNormKummerCocycles.change_preimage_kernel_coboundary (K : Type) [Field K] [CharZero K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    (a : RationalPoints) (b b' : Points K)
    (hb : b ≫ φ = rationalPoint K a) (hb' : b' ≫ φ = rationalPoint K a) :
    (b' * b⁻¹) ≫ φ = 1 ∧ ∀ σ : K ≃ₐ[ℚ] K,
      difference K b' σ =
        actionHom K σ (b' * b⁻¹) * difference K b σ * (b' * b⁻¹)⁻¹ := by sorry
