-- Prove2me | Theorems.Thm_GlobalTheory_SS_Translates_exists_section_fibre
-- name    : GlobalTheory.SS.Translates.exists_section_fibre
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:19:01.90385+00:00
-- url     : https://prove2.me/theorems/fe7a4c49-9606-4167-95d6-523405463cb0
-- title:
--   Translates: exists section fibre
-- statement:
--   The Translates construction uses the exists section fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/StrictModelTranslatesTwistCompatible.lean#L154-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/StrictModelTranslatesTwistCompatible.lean#L154-L169

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

theorem GlobalTheory.SS.Translates.exists_section_fibre [IsDomain R] [IsLocalRing R] (hR : SH R K) (M : Model R A)
    (y : ↥(pullback M.Y.hom (spMap (IsLocalRing.residue R)))) (hy : IsClosed {y}) :
    ∃ s : 𝟙_ (Over (Sp R)) ⟶ M.Y, s.left (IsLocalRing.closedPoint R) = pullback.fst M.Y.hom (spMap (IsLocalRing.residue R)) y := by sorry
