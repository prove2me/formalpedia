-- Prove2me | Theorems.Thm_GlobalTheory_SS_FrobField_isMonHom_app
-- name    : GlobalTheory.SS.FrobField.isMonHom_app
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:34:33.547164+00:00
-- url     : https://prove2.me/theorems/206ea59e-0a8f-4d01-9f87-4331a09f2da2
-- title:
--   Frob Field: is Mon Hom app
-- statement:
--   The Frob Field construction uses the is Mon Hom app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFrobGBaseChange.lean#L295-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFrobGBaseChange.lean#L295-L302

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

theorem GlobalTheory.SS.FrobField.isMonHom_app {C D : Type*} [Category C] [Category D] [CartesianMonoidalCategory C]
    [CartesianMonoidalCategory D] (P : C ⥤ D) [P.Monoidal] (α : P ⟶ P) (G : C) [MonObj G] :
    IsMonHom (α.app G) := by sorry
