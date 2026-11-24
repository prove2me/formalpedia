-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_FormExtJ_isUnit_mp_omjExt_iff
-- name    : GlobalTheory.CechDR.FormExtJ.isUnit_mp_omjExt_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:14:32.120202+00:00
-- url     : https://prove2.me/theorems/5d4d462d-626a-46be-ae0c-320e8c08ed3a
-- title:
--   Form Ext J: is Unit mp omj Ext iff
-- statement:
--   The Form Ext J construction uses the is Unit mp omj Ext iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsUnitMpOmjExtIff.lean#L79-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsUnitMpOmjExtIff.lean#L79-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitMpOmjExtIff
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
open CategoryTheory KaehlerDifferential
open GlobalTheory GlobalTheory.CechDR GlobalTheory.CechDR.FormExtJ
open GlobalTheory.CatCoh
attribute [local instance] opModJ isCentralScalarJ isScalarTowerJ
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (j : ℕ)

theorem GlobalTheory.CechDR.FormExtJ.isUnit_mp_omjExt_iff {T S : C} (u : T ⟶ S) (c : (omjExt F j).obj T) :
    IsUnit (mp (omjExt F j) u c) ↔ IsUnit (mp F u c.fst) := by sorry
