-- Prove2me | Theorems.Thm_GlobalTheory_SS_ModelPoints_spMap_cancel
-- name    : GlobalTheory.SS.ModelPoints.spMap_cancel
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:36:51.580146+00:00
-- url     : https://prove2.me/theorems/962e0a8b-a0be-42e3-8617-f94f3208f0db
-- title:
--   Model Points: sp Map cancel
-- statement:
--   The Model Points construction uses the sp Map cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GrpSchemePointsModelOverField.lean#L56-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GrpSchemePointsModelOverField.lean#L56-L63

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpSchemePointsModelOverField
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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.ModelPoints

theorem GlobalTheory.SS.ModelPoints.spMap_cancel {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {g : B →+* C}
    (hg : Function.Injective g) {a b : Sp B ⟶ Sp A} (e : spMap g ≫ a = spMap g ≫ b) : a = b := by sorry
