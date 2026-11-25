-- Prove2me | Theorems.Thm_GlobalTheory_SS_LawDef_exists_section_general
-- name    : GlobalTheory.SS.LawDef.exists_section_general
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:10:48.234122+00:00
-- url     : https://prove2.me/theorems/7f885cc9-bca5-49d7-9d5b-47175354d37f
-- title:
--   Law Def: exists section general
-- statement:
--   The Law Def construction uses the exists section general property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ModelGroupLawDefinedAtTranslate.lean#L264-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ModelGroupLawDefinedAtTranslate.lean#L264-L280

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelGroupLawDefinedAtTranslate
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
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.LawDef
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' : Over (Sp K)}
variable [IsLocalRing R]

theorem GlobalTheory.SS.LawDef.exists_section_general [IsDomain R] (hR : SH R K) {M : Model R A} (hi : M.Irr) {f : A ⟶ A}
    (hf : GenIso M M f) {V₁ V₂ : Set M.Y.left} (o₁ : IsOpen V₁) (o₂ : IsOpen V₂) (n₁ : (M.sp ∩ V₁).Nonempty)
    (n₂ : (M.sp ∩ V₂).Nonempty) :
    ∃ (s : 𝟙_ (Over (Sp R)) ⟶ M.Y), sp0 s ∈ V₁ ∧ ∀ p, Sec M p s → ∃ t, Sec M (p ≫ f) t ∧ sp0 t ∈ V₂ := by sorry
