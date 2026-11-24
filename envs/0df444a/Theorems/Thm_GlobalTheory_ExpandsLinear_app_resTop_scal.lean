-- Prove2me | Theorems.Thm_GlobalTheory_ExpandsLinear_app_resTop_scal
-- name    : GlobalTheory.ExpandsLinear.app_resTop_scal
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:10:48.814175+00:00
-- url     : https://prove2.me/theorems/a51c579f-2b19-451a-84cf-380bf450bb6c
-- title:
--   Expands Linear: app res Top scal
-- statement:
--   The Expands Linear construction uses the app res Top scal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ScalCompSpecMap.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ScalCompSpecMap.lean#L36-L42

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtIffStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ScalCompSpecMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.ExpandsLinear

theorem GlobalTheory.ExpandsLinear.app_resTop_scal {R : Type} [CommRing R] {Y Y' : Scheme.{0}} (h : Y' ⟶ Y)
    (p : Y ⟶ Spec (CommRingCat.of R)) (W : Y.Opens) (r : R) :
    (h.app W).hom (resTop W (scal p r)) = resTop _ (scal (h ≫ p) r) := by sorry
