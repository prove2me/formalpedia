-- Prove2me | Theorems.Thm_GlobalTheory_SS_SectionTranslation_isoAt_slice
-- name    : GlobalTheory.SS.SectionTranslation.isoAt_slice
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:35:59.689768+00:00
-- url     : https://prove2.me/theorems/009f0dfe-46c8-4af7-93d7-99fe8bba6d1f
-- title:
--   Section Translation: iso At slice
-- statement:
--   The Section Translation construction uses the iso At slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TranslationBySection.lean#L104-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TranslationBySection.lean#L104-L160

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection
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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.SectionTranslation
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}

theorem GlobalTheory.SS.SectionTranslation.isoAt_slice [IsDomain R] [IsFractionRing R K] (M : Model R A) (s : 𝟙_ (Over (Sp R)) ⟶ M.Y)
    (a : 𝟙_ (Over (Sp K)) ⟶ A) (ha : a.left ≫ M.j = spMap (algebraMap R K) ≫ s.left)
    (f : A ⊗ A ⟶ A ⊗ A) (hf : f ≫ fst A A = fst A A) (y : M.Y.left)
    (h : IsoAt (M.prod M) (M.prod M) f ((lift (toUnit M.Y ≫ s) (𝟙 M.Y)).left y)) :
    IsoAt M M (lift (toUnit A ≫ a) (𝟙 A) ≫ f ≫ snd A A) y := by sorry
