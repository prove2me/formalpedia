-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_IsPullO_eq_pullHO1
-- name    : GlobalTheory.CechDR.IsPullO.eq_pullHO1
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:10:39.431993+00:00
-- url     : https://prove2.me/theorems/7c64a8a0-cc7c-466b-b012-b72a0cf9d28e
-- title:
--   Is Pull O: eq pull HO1
-- statement:
--   The Is Pull O construction uses the eq pull HO1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUniqueIsPullForm.lean#L95-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUniqueIsPullForm.lean#L95-L96

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

theorem GlobalTheory.CechDR.IsPullO.eq_pullHO1 {c : HO1 s} {c' : HO1 s'} (e : IsPullO h c c') : c' = pullHO1 h c := by sorry
