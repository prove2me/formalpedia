-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualReflectionDiamondRelation_reflectionAlgEquiv_conjugates_diamond
-- name    : MazurTransfer.Order13ActualReflectionDiamondRelation.reflectionAlgEquiv_conjugates_diamond
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T21:23:33.96286+00:00
-- url     : https://prove2.me/theorems/0d2d0cd5-cc39-4a51-b48e-61dc50c8819a
-- title:
--   The literal reflection conjugates diamond to its inverse on the actual function field
-- statement:
--   Let $K$ be a field of characteristic zero and let $a$ be an original reflection parameter. On the actual curve function field, write $r_a$ for the reflection algebra automorphism and $d$ for the diamond automorphism. Then
--   \[r_a d r_a=d^{-1}.\]
--   This relation provides the dihedral symmetry used to compare the two nineteen-norm kernels.
-- source:
--   MazurTheorem Order13ActualReflectionDiamondRelation.reflectionAlgEquiv_conjugates_diamond with seven exact original coordinate and composition helper propositions; original official Anthropic FLT function-field interfaces preserved; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualReflectionFunctionFieldOriginalDataAndConstructorCertificates20261018
import Definitions.Def_MazurTransfer_Order13ReflectionDiamondParameterOriginalDataAndConstructorCertificatesMinimalPublicNamespaceV220261018
noncomputable section
universe u
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13ReflectionParameter MazurTransfer.Order13ActualReflectionFunctionField
open MazurTransfer.Order13FieldDiamondFunctionFieldAutomorphism

theorem MazurTransfer.Order13ActualReflectionDiamondRelation.reflectionAlgEquiv_conjugates_diamond (K : Type u) [Field K] [CharZero K] (a : ReflectionParameter K) :
    reflectionAlgEquiv K a * diamondAlgEquiv K * reflectionAlgEquiv K a = (diamondAlgEquiv K)⁻¹ := by sorry
