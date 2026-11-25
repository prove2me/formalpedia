-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_IsPullForm_eq_pullForm
-- name    : GlobalTheory.CechDR.IsPullForm.eq_pullForm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:10:47.106627+00:00
-- url     : https://prove2.me/theorems/1090aa64-972c-43ca-8e68-395d02eab696
-- title:
--   Is Pull Form: eq pull Form
-- statement:
--   The Is Pull Form construction uses the eq pull Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUniqueIsPullForm.lean#L98-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUniqueIsPullForm.lean#L98-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RestrictPull1InjectiveOfSepGlue
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_Pull1RestrictSurjectiveOfComma
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CompatFamilyExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CocycleOneFormsCoboundaryOfRestrict
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RestrictGlob1Bijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PullHyp1RestrictInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PullHyp1RestrictSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SepOfFactoringCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlueCommaOfBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCocycleCoboundaryCommaLocalBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasLocOAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FormPowSmulEqZeroOfResBasicOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocalizationOfData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwoFormExistsPowSmulEqZeroOfIsLocalization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PairCoverAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPairBelowTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.CechDR
open CatCoh
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ)

theorem GlobalTheory.CechDR.IsPullForm.eq_pullForm {ω : GlobForm s} {ω' : GlobForm s'} (e : IsPullForm h ω ω') :
    ω' = pullForm h ω := by sorry
