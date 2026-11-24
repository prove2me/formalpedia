-- Prove2me | Theorems.Thm_GlobalTheory_SS_Translates_exists_translation
-- name    : GlobalTheory.SS.Translates.exists_translation
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:18:50.177803+00:00
-- url     : https://prove2.me/theorems/8da12acd-b369-4d6c-9527-f12a85f5e682
-- title:
--   Translates: exists translation
-- statement:
--   The Translates construction uses the exists translation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/StrictModelTranslatesTwistCompatible.lean#L301-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/StrictModelTranslatesTwistCompatible.lean#L301-L338

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
variable [GrpObj A] [IsCommMonObj A]

theorem GlobalTheory.SS.Translates.exists_translation [IsDomain R] [IsLocalRing R] (hR : SH R K) (hA : IsAbelianScheme A) {M : Model R A}
    (hM : Strict M) (s s' : 𝟙_ (Over (Sp R)) ⟶ M.Y) {W : Scheme.{0}} (k : W ⟶ M.Y.left) [IsOpenImmersion k]
    {q : W} (hq : k q ∈ M.sp) :
    ∃ (c : 𝟙_ (Over (Sp K)) ⟶ A) (X : Scheme.{0}) (i g : X ⟶ M.Y.left) (o : X) (q' : W),
      IsOpenImmersion i ∧ IsOpenImmersion g ∧ Ext M M (transl c).hom i g ∧
      i o = s.left (IsLocalRing.closedPoint R) ∧ g o = k q' ∧
      IsoAt M M (transl c).hom (s'.left (IsLocalRing.closedPoint R)) := by sorry
