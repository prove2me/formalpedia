-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_FormExt_isUnit_mp_omExt_iff
-- name    : GlobalTheory.CechDR.FormExt.isUnit_mp_omExt_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:36:48.832024+00:00
-- url     : https://prove2.me/theorems/fb2e5b1a-a17d-42f2-9d6a-1c7f7089adde
-- title:
--   Form Ext: is Unit mp om Ext iff
-- statement:
--   The Form Ext construction uses the is Unit mp om Ext iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsLocalizationOfData.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsLocalizationOfData.lean#L73-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlueCommaOfBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasLocOAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocalizationOfData
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
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CechDR GlobalTheory.CechDR.FormExt
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem GlobalTheory.CechDR.FormExt.isUnit_mp_omExt_iff {T S : C} (u : T ⟶ S) (c : (omExt F).obj T) :
    IsUnit (mp (omExt F) u c) ↔ IsUnit (mp F u c.fst) := by sorry
