-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_FormExtJ_hasLoc_omjExt
-- name    : GlobalTheory.CechDR.FormExtJ.hasLoc_omjExt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:59:18.927805+00:00
-- url     : https://prove2.me/theorems/fc478ff1-eba9-437b-a8b7-5936bb06373c
-- title:
--   Form Ext J: has Loc omj Ext
-- statement:
--   The Form Ext J construction uses the has Loc omj Ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasLocalisationAtElementsTrivSqZeroExtForms.lean#L75-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasLocalisationAtElementsTrivSqZeroExtForms.lean#L75-L112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocalizationOfData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitMpOmjExtIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasLocalisationAtElementsTrivSqZeroExtForms
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

theorem GlobalTheory.CechDR.FormExtJ.hasLoc_omjExt (H : Desc.HasLoc F) : Desc.HasLoc (omjExt F j) := by sorry
