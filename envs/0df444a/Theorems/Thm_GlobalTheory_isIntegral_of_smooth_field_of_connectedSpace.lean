-- Prove2me | Theorems.Thm_GlobalTheory_isIntegral_of_smooth_field_of_connectedSpace
-- name    : GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:27:22.678455+00:00
-- url     : https://prove2.me/theorems/48689ec4-840a-421a-84e2-0448c9c8bfb4
-- title:
--   Global Theory: is Integral of smooth field of connected Space
-- statement:
--   The Global Theory construction uses the is Integral of smooth field of connected Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIntegralOfSmoothFieldOfConnectedSpace.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIntegralOfSmoothFieldOfConnectedSpace.lean#L15-L21

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

theorem GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace {K : Type u} [Field K] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of K)) [Smooth g] [ConnectedSpace Z] : IsIntegral Z := by sorry
