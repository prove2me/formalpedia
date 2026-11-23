-- Prove2me | Theorems.Thm_GlobalTheory_SS_SectionTranslation_translation_by_section
-- name    : GlobalTheory.SS.SectionTranslation.translation_by_section
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:52:02.567299+00:00
-- url     : https://prove2.me/theorems/b2264481-ff46-4f60-a202-dd1050cd3c89
-- title:
--   Section Translation: translation by section
-- statement:
--   The Section Translation construction uses the translation by section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TranslationBySection.lean#L169-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TranslationBySection.lean#L169-L187

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

theorem GlobalTheory.SS.SectionTranslation.translation_by_section : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, Strict M → ∀ (s : 𝟙_ (Over (Sp R)) ⟶ M.Y), ∃ a : (𝟙_ (Over (Sp K)) ⟶ A), a.left ≫ M.j = spMap (algebraMap R K) ≫ s.left ∧ GenIso M M (transl a).hom ∧ ∀ (y : M.Y.left) (b : Bool), IsoAt (M.prod M) (M.prod M) (shear A b) ((lift (toUnit M.Y ≫ s) (𝟙 M.Y)).left y) → IsoAt M M (if b then (transl a).hom else (transl a).inv) y := by sorry
