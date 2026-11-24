-- Prove2me | Theorems.Thm_GlobalTheory_ZM_NearBuild_exists_retraction_away
-- name    : GlobalTheory.ZM.NearBuild.exists_retraction_away
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:55:04.724022+00:00
-- url     : https://prove2.me/theorems/710c5cf9-46df-403e-b41b-f700089c3cb7
-- title:
--   Near Build: exists retraction away
-- statement:
--   The Near Build construction uses the exists retraction away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsRetractionNearOfUniquePoint.lean#L72-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsRetractionNearOfUniquePoint.lean#L72-L104

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AlgebraMapSurjectiveOfUnramifiedOfUniquePoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DenseOfDenseP
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsRetractionNearOfUniquePoint
import Theorems.Thm_GlobalTheory_ZM_NearBuild_Den_loc
import Theorems.Thm_GlobalTheory_ZM_NearBuild_FibData_comp

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
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.NearBuild

theorem GlobalTheory.ZM.NearBuild.exists_retraction_away (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
    (hinj : Function.Injective (algebraMap R B)) (f : R)
    (hf : ∀ b : B, ∃ a : R, algebraMap R B a = algebraMap R B f * b) :
    ∃ r : B →+* Localization.Away f, r.comp (algebraMap R B) = loc f := by sorry
