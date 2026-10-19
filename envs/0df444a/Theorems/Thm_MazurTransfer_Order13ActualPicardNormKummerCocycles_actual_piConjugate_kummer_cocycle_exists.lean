-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardNormKummerCocycles_actual_piConjugate_kummer_cocycle_exists
-- name    : MazurTransfer.Order13ActualPicardNormKummerCocycles.actual_piConjugate_kummer_cocycle_exists
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T22:03:36.602994+00:00
-- url     : https://prove2.me/theorems/bea8d703-1a7a-4aba-a33f-3b4b5d03b3a9
-- title:
--   Existence of the actual pi-bar norm Kummer cocycle with exponent nineteen
-- statement:
--   Let P be the same actual rational represented Picard group scheme, K an algebraically closed characteristic-zero field, and a a rational point. For the original norm map \bar\pi, choose b in P(K) over a and set c(sigma)=sigma(b)b inverse. There exists such b for which $$\bar\pi(b)=a_K,\quad \bar\pi(c(\sigma))=1,\quad c(\sigma)^{19}=1,$$ $$c(\sigma\tau)=c(\sigma)\sigma(c(\tau)),\qquad c(1)=1.$$ Thus the preimage difference is an algebraic cocycle valued in the actual norm kernel, killed by nineteen. The named downstream consumers are continuous Kummer cocycles and norm Selmer descent.
-- source:
--   Complete original MazurTheorem Order13ActualPicardNormKummerCocycles.actual_piConjugate_kummer_cocycle_exists statement and main proof. Same actual Picard and original point/action/difference constructors; six helper full types compared separately. Original constructor values and group provider audited. Official Anthropic FLT Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

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
local instance publicPiConjugateKummerStatementProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance publicPiConjugateKummerStatementProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance publicPiConjugateKummerStatementProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance publicPiConjugateKummerStatementProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open MazurTransfer.Order13ActualPicardNormKummerCocycles

theorem MazurTransfer.Order13ActualPicardNormKummerCocycles.actual_piConjugate_kummer_cocycle_exists (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (a : RationalPoints) :
    ∃ b : Points K, b ≫ schemePiConjugate = rationalPoint K a ∧
      (∀ σ : K ≃ₐ[ℚ] K,
        difference K b σ ≫ schemePiConjugate = 1 ∧ (difference K b σ) ^ 19 = 1) ∧
      (∀ σ τ : K ≃ₐ[ℚ] K,
        difference K b (σ * τ) = difference K b σ * actionHom K σ (difference K b τ)) ∧
      difference K b 1 = 1 := by sorry
