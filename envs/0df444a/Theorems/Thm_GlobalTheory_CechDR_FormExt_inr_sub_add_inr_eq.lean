-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_FormExt_inr_sub_add_inr_eq
-- name    : GlobalTheory.CechDR.FormExt.inr_sub_add_inr_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:59:59.85406+00:00
-- url     : https://prove2.me/theorems/19ec9362-fd39-4a00-859b-27b533b4b50a
-- title:
--   Form Ext: inr sub add inr eq
-- statement:
--   The Form Ext construction uses the inr sub add inr eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneFormsTwoCocycleCoboundaryOfRestrict.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneFormsTwoCocycleCoboundaryOfRestrict.lean#L22-L26

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

theorem GlobalTheory.CechDR.FormExt.inr_sub_add_inr_eq {A M : Type} [AddCommGroup A] [AddCommGroup M] {x y z w : M}
    (h : x - y + z = w) :
    (TrivSqZeroExt.inr x : TrivSqZeroExt A M) - TrivSqZeroExt.inr y + TrivSqZeroExt.inr z =
      TrivSqZeroExt.inr w := by sorry
