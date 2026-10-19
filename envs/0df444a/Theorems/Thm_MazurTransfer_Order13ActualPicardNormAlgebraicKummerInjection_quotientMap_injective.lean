-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardNormAlgebraicKummerInjection_quotientMap_injective
-- name    : MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection.quotientMap_injective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T22:58:27.962072+00:00
-- url     : https://prove2.me/theorems/a057e304-f6cc-463f-841a-337bd924d5ea
-- title:
--   The original actual rational norm quotient maps injectively into algebraic H1
-- statement:
--   Let P be the same actual rational Picard group scheme, K a Galois extension of Q of characteristic zero, and phi an internal group endomorphism with surjective K-point map. The original quotient-class map is injective: $$P(\mathbb Q)/\varphi(P(\mathbb Q))\ \hookrightarrow\ H^1(\operatorname{Aut}_{\mathbb Q}(K),\ker\varphi(K)).$$ It uses the original norm quotient, chosen lift class and kernel action. The named downstream consumers are the concrete pi and pi-bar Kummer embeddings and continuous norm Selmer injections.
-- source:
--   Complete original MazurTheorem Order13ActualPicardNormAlgebraicKummerInjection.quotientMap_injective statement and proof, preserving the original Galois and surjectivity hypotheses. All original quotient/class constructors and their complete values are independently compared; the final full type and original group/action providers are compared as well. Official Anthropic FLT Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the rational quotient by an actual norm map injects
into Mathlib algebraic H1 of its actual geometric norm kernel.
Continuity and local conditions are separate obligations.
Named downstream consumer: continuous Kummer and Selmer bounds.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardAlgebraicNormQuotientKummerData
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
local instance publicActualNormQuotientKummerInjectiveStatementProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance publicActualNormQuotientKummerInjectiveStatementProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance publicActualNormQuotientKummerInjectiveStatementProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance publicActualNormQuotientKummerInjectiveStatementProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
open Order13ActualPicardNormAlgebraicCohomology
open MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection

theorem MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection.quotientMap_injective (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    (hsurj : Function.Surjective (normHom K φ)) : Function.Injective (quotientMap K φ hsurj) := by sorry
