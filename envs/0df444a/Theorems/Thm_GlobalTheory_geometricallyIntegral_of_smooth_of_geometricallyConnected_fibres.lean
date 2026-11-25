-- Prove2me | Theorems.Thm_GlobalTheory_geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres
-- name    : GlobalTheory.geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:28:00.255187+00:00
-- url     : https://prove2.me/theorems/fe8ca82f-56e6-4b8c-80a2-04db1ccae1e7
-- title:
--   Global Theory: geometrically Integral of smooth of geometrically Connected fibres
-- statement:
--   The Global Theory construction uses the geometrically Integral of smooth of geometrically Connected fibres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIntegralOfSmoothFieldOfConnectedSpace.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIntegralOfSmoothFieldOfConnectedSpace.lean#L23-L28

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

theorem GlobalTheory.geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres {X S : Scheme.{u}}
    (f : X ⟶ S) [Smooth f] [GeometricallyConnected f] : GeometricallyIntegral f := by sorry
