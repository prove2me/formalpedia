-- Prove2me | Theorems.Thm_GlobalTheory_SS_FrobField_appLE_congr_hom
-- name    : GlobalTheory.SS.FrobField.appLE_congr_hom
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:33:30.264594+00:00
-- url     : https://prove2.me/theorems/824dd9d2-06d0-4849-8809-452c4e92c249
-- title:
--   Frob Field: app LE congr hom
-- statement:
--   The Frob Field construction uses the app LE congr hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFrobGBaseChange.lean#L206-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFrobGBaseChange.lean#L206-L208

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFrobGBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.FrobField

theorem GlobalTheory.SS.FrobField.appLE_congr_hom {X Y : Scheme.{0}} {φ ψ : X ⟶ Y} (e : φ = ψ) (V : Y.Opens) (U : X.Opens)
    (h : U ≤ φ ⁻¹ᵁ V) (h' : U ≤ ψ ⁻¹ᵁ V) : φ.appLE V U h = ψ.appLE V U h' := by sorry
