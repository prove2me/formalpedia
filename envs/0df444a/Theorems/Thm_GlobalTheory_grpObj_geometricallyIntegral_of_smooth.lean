-- Prove2me | Theorems.Thm_GlobalTheory_grpObj_geometricallyIntegral_of_smooth
-- name    : GlobalTheory.grpObj_geometricallyIntegral_of_smooth
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:27:59.676309+00:00
-- url     : https://prove2.me/theorems/122e500c-dbb4-45ed-a7bb-2bc411e16bcd
-- title:
--   Global Theory: grp Obj geometrically Integral of smooth
-- statement:
--   The Global Theory construction uses the grp Obj geometrically Integral of smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIntegralOfSmoothFieldOfConnectedSpace.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIntegralOfSmoothFieldOfConnectedSpace.lean#L30-L32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
universe u

theorem GlobalTheory.grpObj_geometricallyIntegral_of_smooth (S : Scheme.{0}) (H : Over S) [GrpObj H]
    [Smooth H.hom] [GeometricallyConnected H.hom] : GeometricallyIntegral H.hom := by sorry
