-- Prove2me | Theorems.Thm_GlobalTheory_KS_GlueDer_res_app
-- name    : GlobalTheory.KS.GlueDer.res_app
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:19:27.648746+00:00
-- url     : https://prove2.me/theorems/d1d1ceb5-1ae3-4164-b70b-56de1aaff644
-- title:
--   Glue Der: res app
-- statement:
--   The Glue Der construction uses the res app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGlobalLocDerOfIsCob.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGlobalLocDerOfIsCob.lean#L23-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueInvariantVectorFieldOfTangentStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGlobalLocDerOfIsCob
import Theorems.Thm_GlobalTheory_ConstThickening_res_app

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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.GlueDer

theorem GlobalTheory.KS.GlueDer.res_app {Y X : Scheme.{0}} (m : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (h' : m ⁻¹ᵁ V ≤ m ⁻¹ᵁ U) (f : Γ(X, U)) :
    resG Y h' ((m.app U).hom f) = (m.app V).hom (resG X h f) := by sorry
