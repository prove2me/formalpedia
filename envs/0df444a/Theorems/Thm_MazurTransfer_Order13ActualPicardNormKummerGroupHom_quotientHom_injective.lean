-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardNormKummerGroupHom_quotientHom_injective
-- name    : MazurTransfer.Order13ActualPicardNormKummerGroupHom.quotientHom_injective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T23:16:44.068699+00:00
-- url     : https://prove2.me/theorems/105933a8-43ea-4fc0-99fc-888ee87dc258
-- title:
--   The original actual norm Kummer quotient group homomorphism is injective
-- statement:
--   Let P be the same actual rational Picard, K a Galois extension of Q of characteristic zero, and phi an internal group endomorphism whose K-point map is surjective. The original Kummer quotient homomorphism has injective underlying function: $$P(\mathbb Q)/\varphi(P(\mathbb Q))\hookrightarrow H^1(\operatorname{Aut}_{\mathbb Q}(K),\ker\varphi(K)).$$ Thus it is an injective group homomorphism, with H1 written multiplicatively in the formal homomorphism. The named downstream consumers are both concrete algebraic-closure norm Kummer group maps and continuous norm Selmer group bounds.
-- source:
--   Complete original MazurTheorem Order13ActualPicardNormKummerGroupHom.quotientHom_injective statement and proof. Same original Kummer group homomorphism and quotient constructor values, with all relevant group/action and algebraic Kummer dependency providers compared. Complete original final type is compared independently. Official Anthropic FLT Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual rational norm quotient Kummer injection
preserves the group law in Mathlib algebraic H1. Continuity and local
conditions remain separate obligations.
Named downstream consumer: continuous Kummer and Selmer group bounds.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKummerGenericGroupHomData
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance publicNormKummerQuotientGroupHomInjectiveStatementProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance publicNormKummerQuotientGroupHomInjectiveStatementProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance publicNormKummerQuotientGroupHomInjectiveStatementProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance publicNormKummerQuotientGroupHomInjectiveStatementProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
open Order13ActualPicardNormAlgebraicCohomology
open Order13ActualPicardNormAlgebraicKummerInjection
open MazurTransfer.Order13ActualPicardNormKummerGroupHom

theorem MazurTransfer.Order13ActualPicardNormKummerGroupHom.quotientHom_injective (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    (hsurj : Function.Surjective (normHom K φ)) : Function.Injective (quotientHom K φ hsurj) := by sorry
