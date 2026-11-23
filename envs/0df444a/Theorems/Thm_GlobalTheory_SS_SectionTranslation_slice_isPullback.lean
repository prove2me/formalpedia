-- Prove2me | Theorems.Thm_GlobalTheory_SS_SectionTranslation_slice_isPullback
-- name    : GlobalTheory.SS.SectionTranslation.slice_isPullback
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:39:53.812247+00:00
-- url     : https://prove2.me/theorems/49cd30fe-d910-4ff0-8b10-d5eb54d0c55e
-- title:
--   Section Translation: slice is Pullback
-- statement:
--   The Section Translation construction uses the slice is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TranslationBySection.lean#L92-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TranslationBySection.lean#L92-L102

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

theorem GlobalTheory.SS.SectionTranslation.slice_isPullback {S : Scheme.{0}} (Y : Over S) (s : 𝟙_ (Over S) ⟶ Y) :
    IsPullback (lift (toUnit Y ≫ s) (𝟙 Y)).left Y.hom (fst Y Y).left s.left := by sorry
