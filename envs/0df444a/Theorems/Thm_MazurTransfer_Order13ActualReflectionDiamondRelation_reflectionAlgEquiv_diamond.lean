-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualReflectionDiamondRelation_reflectionAlgEquiv_diamond
-- name    : MazurTransfer.Order13ActualReflectionDiamondRelation.reflectionAlgEquiv_diamond
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T22:55:59.644241+00:00
-- url     : https://prove2.me/theorems/27582708-11e1-49aa-85fc-3d36a3d505a8
-- title:
--   Reflection composed with diamond is the next coefficient-orbit reflection
-- statement:
--   For every characteristic-zero field $K$ and original reflection parameter $a$, let $r_a$ denote the literal reflection and $d$ the literal diamond automorphism on the same actual curve function field. Then
--   \[r_a d=r_{D(a)},\]
--   where $D$ is the original diamond transformation of reflection parameters. This composition formula controls the reflection line under the primitive thirteenth-root generator orbit.
-- source:
--   MazurTheorem Order13ActualReflectionDiamondRelation.reflectionAlgEquiv_diamond, with its five exact original coordinate and function-field comparison helper propositions; complete original universe-polymorphic statement retained; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualReflectionFunctionFieldOriginalDataAndConstructorCertificates20261018
import Definitions.Def_MazurTransfer_Order13ReflectionDiamondParameterOriginalDataAndConstructorCertificatesMinimalPublicNamespaceV220261018
noncomputable section
universe u
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13ReflectionParameter MazurTransfer.Order13ActualReflectionFunctionField
open MazurTransfer.Order13FieldDiamondFunctionFieldAutomorphism MazurTransfer.Order13ReflectionParameterArithmetic

theorem MazurTransfer.Order13ActualReflectionDiamondRelation.reflectionAlgEquiv_diamond (K : Type u) [Field K] [CharZero K] (a : ReflectionParameter K) :
    reflectionAlgEquiv K a * diamondAlgEquiv K = reflectionAlgEquiv K (diamondParameter a) := by sorry
