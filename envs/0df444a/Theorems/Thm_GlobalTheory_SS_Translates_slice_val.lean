-- Prove2me | Theorems.Thm_GlobalTheory_SS_Translates_slice_val
-- name    : GlobalTheory.SS.Translates.slice_val
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:18:44.937528+00:00
-- url     : https://prove2.me/theorems/f912077f-8919-4f3a-8e1a-69da6457cabc
-- title:
--   Translates: slice val
-- statement:
--   The Translates construction uses the slice val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/StrictModelTranslatesTwistCompatible.lean#L231-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/StrictModelTranslatesTwistCompatible.lean#L231-L246

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenImmersionOfSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_StrictModelTranslatesTwistCompatible
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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Translates
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' : Over (Sp K)}

theorem GlobalTheory.SS.Translates.slice_val [IsDomain R] [IsFractionRing R K] (M : Model R A) (σ : M.Y ⟶ M.Y ⊗ M.Y) (σ' : A ⟶ A ⊗ A)
    (hσ : M.j ≫ σ.left = σ'.left ≫ pj M M) (F : A ⊗ A ⟶ A ⊗ A) {f : A ⟶ A} (hf : σ' ≫ F ≫ snd A A = f)
    {X X' : Scheme.{0}} {i g : X ⟶ M.Y.left} {I G : X' ⟶ (M.Y ⊗ M.Y).left} [IsOpenImmersion i] [IsOpenImmersion I]
    (h : Ext M M f i g) (h' : Ext (M.prod M) (M.prod M) F I G) {o : X} {o' : X'} (e : I o' = σ.left (i o)) :
    g o = (snd M.Y M.Y).left (G o') := by sorry
