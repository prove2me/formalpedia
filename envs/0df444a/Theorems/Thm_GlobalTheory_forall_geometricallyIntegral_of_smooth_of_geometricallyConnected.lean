-- Prove2me | Theorems.Thm_GlobalTheory_forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
-- name    : GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:44:10.168954+00:00
-- url     : https://prove2.me/theorems/fa9e071b-91b8-4462-9009-751ead5f97c3
-- title:
--   Global Theory: forall geometrically Integral of smooth of geometrically Connected
-- statement:
--   The Global Theory construction uses the forall geometrically Integral of smooth of geometrically Connected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ForallGeometricallyIntegralOfSmoothOfGeometrical.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ForallGeometricallyIntegralOfSmoothOfGeometrical.lean#L11-L14

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f →
      GeometricallyIntegral f := by sorry
