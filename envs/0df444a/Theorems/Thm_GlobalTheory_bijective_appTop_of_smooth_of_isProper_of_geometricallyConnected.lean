-- Prove2me | Theorems.Thm_GlobalTheory_bijective_appTop_of_smooth_of_isProper_of_geometricallyConnected
-- name    : GlobalTheory.bijective_appTop_of_smooth_of_isProper_of_geometricallyConnected
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:06:51.40303+00:00
-- url     : https://prove2.me/theorems/dbddf30f-bb46-4f62-b479-b45ba0f5ef99
-- title:
--   Global Theory: bijective app Top of smooth of is Proper of geometrically Connected
-- statement:
--   The Global Theory construction uses the bijective app Top of smooth of is Proper of geometrically Connected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/BijectiveAppTopOfSmoothOfIsProperOfGeometrically.lean#L15-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/BijectiveAppTopOfSmoothOfIsProperOfGeometrically.lean#L15-L26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_BijectiveAppTopOfSmoothOfIsProperOfGeometrically
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory

theorem GlobalTheory.bijective_appTop_of_smooth_of_isProper_of_geometricallyConnected :
    ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K), Smooth p → IsProper p →
      GeometricallyConnected p → Function.Bijective p.appTop.hom := by sorry
