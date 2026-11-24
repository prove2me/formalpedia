-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_FormExtJ_ker_keyJ
-- name    : GlobalTheory.CechDR.FormExtJ.ker_keyJ
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:59:26.244734+00:00
-- url     : https://prove2.me/theorems/32af41cb-6943-4c74-a1a9-eb370f7bf716
-- title:
--   Form Ext J: ker key J
-- statement:
--   The Form Ext J construction uses the ker key J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasLocalisationAtElementsTrivSqZeroExtForms.lean#L66-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasLocalisationAtElementsTrivSqZeroExtForms.lean#L66-L73

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

theorem GlobalTheory.CechDR.FormExtJ.ker_keyJ {T : C} (c x : TrivSqZeroExt (F.obj T) (Om R (F.obj T) j)) (m₁ m₂ : ℕ)
    (h₁ : c.fst ^ m₁ * x.fst = 0) (h₂ : c.fst ^ m₂ • x.snd = 0) : c ^ (m₁ + m₂ + 1) * x = 0 := by sorry
