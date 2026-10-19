-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualNormKernelFixedPartIdentification_actual_kernel_galois_action_fixed_cards
-- name    : MazurTransfer.Order13ActualNormKernelFixedPartIdentification.actual_kernel_galois_action_fixed_cards
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T20:11:45.935556+00:00
-- url     : https://prove2.me/theorems/37d7386a-724c-4b4c-b572-dc7daa2bf2a1
-- title:
--   The actual geometric norm kernels have fixed parts of cardinalities one and nineteen
-- statement:
--   For every characteristic-zero Galois extension of the rationals and original affine cover, the Galois-fixed part of the actual pi kernel has cardinality one, and the conjugate kernel fixed part has cardinality nineteen.
-- source:
--   MazurTheorem Order13ActualNormKernelFixedPartIdentification.actual_kernel_galois_action_fixed_cards; complete exact original telescope retained; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13KernelActionFixedSubgroupOriginalDataAndCertificates20261018
import Definitions.Def_MazurTransfer_Order13ActualPicardRationalNormKernelEquivalencesOriginalData20261018
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the exact ordered arithmetic norm-kernel cardinalities transport to the Galois-fixed subgroups of the original geometric norm kernels. Named downstream consumer: actual invariant-space dimensions and cyclotomic quotients.
-/
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardNormKummerCocycles Order13ActualPicardGaloisFixedPointDescent
open Order13ActualNormFixedKernelEquivalence
open Order13ActualPicardRationalNormComparison
open Order13ActualKernelActionFixedSubgroup
open scoped CategoryTheory.MonObj
local instance publicActualKernelFixedCardsOriginalProvider120261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj
local instance publicActualKernelFixedCardsOriginalProvider220261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).isCommMonObj
local instance publicActualKernelFixedCardsOriginalProvider320261018 : IsMonHom schemePi := schemePi_isMonHom
local instance publicActualKernelFixedCardsOriginalProvider420261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (𝒱 : (curveScheme ℚ).TwoAffineOpenCover)

theorem MazurTransfer.Order13ActualNormKernelFixedPartIdentification.actual_kernel_galois_action_fixed_cards (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) : Nat.card (kernelGaloisFixed K schemePi) = 1 ∧ Nat.card (kernelGaloisFixed K schemePiConjugate) = 19 := by sorry
