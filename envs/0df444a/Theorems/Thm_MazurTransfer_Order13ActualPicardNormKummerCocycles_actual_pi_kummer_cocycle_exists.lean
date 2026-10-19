-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardNormKummerCocycles_actual_pi_kummer_cocycle_exists
-- name    : MazurTransfer.Order13ActualPicardNormKummerCocycles.actual_pi_kummer_cocycle_exists
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T22:03:34.661209+00:00
-- url     : https://prove2.me/theorems/3990cac3-b8fc-455c-8696-ffab1f63b3cd
-- title:
--   Existence of the actual pi norm Kummer cocycle with exponent nineteen
-- statement:
--   Let P be the same actual rational represented Picard group scheme, K an algebraically closed characteristic-zero field, and a a rational point. For the original norm map \pi, choose b in P(K) over a and set c(sigma)=sigma(b)b inverse. There exists such b for which $$\pi(b)=a_K,\quad \pi(c(\sigma))=1,\quad c(\sigma)^{19}=1,$$ $$c(\sigma\tau)=c(\sigma)\sigma(c(\tau)),\qquad c(1)=1.$$ Thus the preimage difference is an algebraic cocycle valued in the actual norm kernel, killed by nineteen. The named downstream consumers are continuous Kummer cocycles and norm Selmer descent.
-- source:
--   Complete original MazurTheorem Order13ActualPicardNormKummerCocycles.actual_pi_kummer_cocycle_exists statement and main proof. Same actual Picard and original point/action/difference constructors; six helper full types compared separately. Original constructor values and group provider audited. Official Anthropic FLT Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

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
local instance publicPiKummerStatementProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance publicPiKummerStatementProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance publicPiKummerStatementProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance publicPiKummerStatementProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open MazurTransfer.Order13ActualPicardNormKummerCocycles

theorem MazurTransfer.Order13ActualPicardNormKummerCocycles.actual_pi_kummer_cocycle_exists (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (a : RationalPoints) :
    ∃ b : Points K, b ≫ schemePi = rationalPoint K a ∧
      (∀ σ : K ≃ₐ[ℚ] K, difference K b σ ≫ schemePi = 1 ∧ (difference K b σ) ^ 19 = 1) ∧
      (∀ σ τ : K ≃ₐ[ℚ] K,
        difference K b (σ * τ) = difference K b σ * actionHom K σ (difference K b τ)) ∧
      difference K b 1 = 1 := by sorry
