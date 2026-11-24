-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_FormExt_surj_key
-- name    : GlobalTheory.CechDR.FormExt.surj_key
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:36:19.352447+00:00
-- url     : https://prove2.me/theorems/14bc1c8d-c8e6-45e9-8110-36973de910b1
-- title:
--   Form Ext: surj key
-- statement:
--   The Form Ext construction uses the surj key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsLocalizationOfData.lean#L77-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsLocalizationOfData.lean#L77-L93

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

theorem GlobalTheory.CechDR.FormExt.surj_key {T T' : C} (l : T ⟶ T') (c : TrivSqZeroExt (F.obj T) Ω[F.obj T⁄R])
    (y : TrivSqZeroExt (F.obj T') Ω[F.obj T'⁄R]) (a₀ : F.obj T) (η₀ : Ω[F.obj T⁄R]) (k₁ k₂ : ℕ)
    (ha : y.fst * mp F l (c.fst ^ k₁) = mp F l a₀) (hη : mp F l (c.fst ^ k₂) • y.snd = p1 F l η₀) :
    y * extMap F l c ^ (k₁ + k₂ + 1) = extMap F l (TrivSqZeroExt.inl (a₀ * c.fst ^ (k₂ + 1)) +
      TrivSqZeroExt.inr ((k₁ + k₂ + 1) • (a₀ * c.fst ^ k₂) • c.snd + c.fst ^ (k₁ + 1) • η₀)) := by sorry
