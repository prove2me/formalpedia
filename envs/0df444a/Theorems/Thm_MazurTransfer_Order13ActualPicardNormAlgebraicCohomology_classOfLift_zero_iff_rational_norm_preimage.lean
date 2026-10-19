-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardNormAlgebraicCohomology_classOfLift_zero_iff_rational_norm_preimage
-- name    : MazurTransfer.Order13ActualPicardNormAlgebraicCohomology.classOfLift_zero_iff_rational_norm_preimage
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T22:32:14.688069+00:00
-- url     : https://prove2.me/theorems/b642bc80-4af6-4606-b88c-50b51fb229d7
-- title:
--   An actual Picard norm lift class vanishes exactly for rational norm images
-- statement:
--   Let P be the same actual rational Picard group scheme, K a Galois extension of Q of characteristic zero, and phi an internal group endomorphism of P. Let a be rational and b in P(K) satisfy phi(b)=a_K. Form the original algebraic cohomology class of c_b(sigma)=sigma(b)b inverse in the geometric norm kernel. Then $$[c_b]=0\ \text{in }H^1(\operatorname{Aut}_{\mathbb Q}(K),\ker\varphi(K))\quad\Longleftrightarrow\quad\exists c\in P(\mathbb Q),\ \varphi(c)=a.$$ No finiteness, étaleness or algebraic-closure assumption is added. The named downstream consumer is the actual rational norm quotient Kummer injection and the norm Selmer bound.
-- source:
--   Complete original MazurTheorem Order13ActualPicardNormAlgebraicCohomology.classOfLift_zero_iff_rational_norm_preimage statement and main proof. Six original full helper types and bodies are retained: scalar-map epimorphism, scalar-extension injectivity, actual rational-point injectivity, the generic invariant-preimage criterion and both intermediate cohomological zero criteria. Original H1 constructors, kernel action, group law and dependency providers are compared fully. Official Anthropic FLT Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0. The exact original Galois context of both intermediate zero criteria is retained, as confirmed by separate original full-type diagnostics.

import Definitions.Def_MazurTransfer_Order13ActualPicardNormAlgebraicCohomologyData
import Definitions.Def_MazurTransfer_Order13ActualPicardRationalFixedPointGroupData
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
local instance publicActualNormH1ZeroStatementProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance publicActualNormH1ZeroStatementProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance publicActualNormH1ZeroStatementProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance publicActualNormH1ZeroStatementProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
open MazurTransfer.Order13ActualPicardNormAlgebraicCohomology

theorem MazurTransfer.Order13ActualPicardNormAlgebraicCohomology.classOfLift_zero_iff_rational_norm_preimage (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a) :
    classOfLift K φ a b hb = 0 ↔ ∃ c : RationalPoints, c ≫ φ = a := by sorry
