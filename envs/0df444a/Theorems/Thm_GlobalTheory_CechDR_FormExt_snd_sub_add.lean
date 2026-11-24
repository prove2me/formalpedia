-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_FormExt_snd_sub_add
-- name    : GlobalTheory.CechDR.FormExt.snd_sub_add
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:59:33.171712+00:00
-- url     : https://prove2.me/theorems/731668fc-933b-482d-932b-6df63aafbb48
-- title:
--   Form Ext: snd sub add
-- statement:
--   The Form Ext construction uses the snd sub add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneFormsTwoCocycleCoboundaryOfRestrict.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneFormsTwoCocycleCoboundaryOfRestrict.lean#L28-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocalizationOfData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitMpOmjExtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneFormsTwoCocycleCoboundaryOfRestrict
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CechDR GlobalTheory.CechDR.FormExt
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

theorem GlobalTheory.CechDR.FormExt.snd_sub_add {A M : Type} [AddCommGroup A] [AddCommGroup M] (a b c : TrivSqZeroExt A M) :
    (a - b + c).snd = a.snd - b.snd + c.snd := by sorry
