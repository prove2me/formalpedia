-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardGaloisFixedPointDescent_rationalToFixed_bijective
-- name    : MazurTransfer.Order13ActualPicardGaloisFixedPointDescent.rationalToFixed_bijective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T22:27:20.163697+00:00
-- url     : https://prove2.me/theorems/4ef77700-e835-4919-acf7-5a9c19fdb459
-- title:
--   Rational points of the actual Picard are exactly its Galois-fixed geometric points
-- statement:
--   Let P be the same actual rational represented Picard group scheme and K a Galois extension of Q of characteristic zero. The original scalar-extension homomorphism into the fixed subgroup is bijective: $$P(\mathbb Q)\ \xrightarrow{\ \sim\ }\ P(K)^{\operatorname{Aut}_{\mathbb Q}(K)}.$$ The theorem concerns the original point, action, subgroup and scalar-extension constructors. The named downstream consumer is the original multiplicative equivalence between rational and fixed points and the rationality step for actual norm Kummer classes.
-- source:
--   Complete original MazurTheorem Order13ActualPicardGaloisFixedPointDescent.rationalToFixed_bijective proof and final type, with the original scalar-map epimorphism, scalar-extension injectivity and actual rational-point injectivity helper types and bodies retained. Original rational/fixed constructors and group provider are compared. Official Anthropic FLT Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

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
local instance publicActualPicardRationalToFixedBijectiveStatementProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance publicActualPicardRationalToFixedBijectiveStatementProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance publicActualPicardRationalToFixedBijectiveStatementProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance publicActualPicardRationalToFixedBijectiveStatementProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open MazurTransfer.Order13ActualPicardGaloisFixedPointDescent

theorem MazurTransfer.Order13ActualPicardGaloisFixedPointDescent.rationalToFixed_bijective (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] : Function.Bijective (rationalToFixed K) := by sorry
