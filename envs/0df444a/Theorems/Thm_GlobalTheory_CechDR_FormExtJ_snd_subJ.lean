-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_FormExtJ_snd_subJ
-- name    : GlobalTheory.CechDR.FormExtJ.snd_subJ
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:59:48.682884+00:00
-- url     : https://prove2.me/theorems/63de6985-d259-4d56-be16-848b95dcc9d0
-- title:
--   Form Ext J: snd sub J
-- statement:
--   The Form Ext J construction uses the snd sub J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HigherFormsOneCocycleCoboundaryOfRestrict.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HigherFormsOneCocycleCoboundaryOfRestrict.lean#L27-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocalizationOfData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitMpOmjExtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HigherFormsOneCocycleCoboundaryOfRestrict
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
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CechDR GlobalTheory.CechDR.FormExtJ
attribute [local instance] opModJ isCentralScalarJ isScalarTowerJ
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (j : ℕ)

theorem GlobalTheory.CechDR.FormExtJ.snd_subJ {T : C} (a b : (omjExt F j).obj T) :
    TrivSqZeroExt.snd (a - b) = TrivSqZeroExt.snd a - TrivSqZeroExt.snd b := by sorry
