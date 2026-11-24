-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_FormExt_mp_omExt_inr
-- name    : GlobalTheory.CechDR.FormExt.mp_omExt_inr
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:59:44.141808+00:00
-- url     : https://prove2.me/theorems/dc7e24d5-23a5-451a-b556-f284b9809e7e
-- title:
--   Form Ext: mp om Ext inr
-- statement:
--   The Form Ext construction uses the mp om Ext inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneFormsTwoCocycleCoboundaryOfRestrict.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneFormsTwoCocycleCoboundaryOfRestrict.lean#L32-L37

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

theorem GlobalTheory.CechDR.FormExt.mp_omExt_inr {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    {T T' : C} (φ : T ⟶ T') (x : Ω[F.obj T⁄R]) :
    mp (omExt F) φ (TrivSqZeroExt.inr x : (omExt F).obj T) =
      (TrivSqZeroExt.inr (p1 F φ x) : (omExt F).obj T') := by sorry
