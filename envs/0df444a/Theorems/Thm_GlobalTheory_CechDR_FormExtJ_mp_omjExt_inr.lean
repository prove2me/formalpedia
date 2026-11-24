-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_FormExtJ_mp_omjExt_inr
-- name    : GlobalTheory.CechDR.FormExtJ.mp_omjExt_inr
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:12:44.125066+00:00
-- url     : https://prove2.me/theorems/194fdf66-e8ae-4cdc-a8c5-7fdca4139e14
-- title:
--   Form Ext J: mp omj Ext inr
-- statement:
--   The Form Ext J construction uses the mp omj Ext inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsUnitMpOmjExtIff.lean#L70-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsUnitMpOmjExtIff.lean#L70-L74

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

theorem GlobalTheory.CechDR.FormExtJ.mp_omjExt_inr {T T' : C} (φ : T ⟶ T') (x : Om R (F.obj T) j) :
    mp (omjExt F j) φ (TrivSqZeroExt.inr x : (omjExt F j).obj T) =
      (TrivSqZeroExt.inr (pOm F j φ x) : (omjExt F j).obj T') := by sorry
