-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_comp_eq_on_chart_of_mul_eq_of_agree
-- name    : FunctorialResolution.EmbeddedResolution.comp_eq_on_chart_of_mul_eq_of_agree
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:25:01.559401+00:00
-- url     : https://prove2.me/theorems/e3301cc1-f11c-4b1f-8f10-c327ccd1426d
-- title:
--   Embedded Resolution: comp eq on chart of mul eq of agree
-- statement:
--   The Embedded Resolution construction uses the comp eq on chart of mul eq of agree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/BlowupChartCongruence.lean#L467-L492
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/BlowupChartCongruence.lean#L467-L492

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupChartPreimages
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_BlowupChartCongruence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
universe u
variable {R : Type u} [CommRing R]

theorem FunctorialResolution.EmbeddedResolution.comp_eq_on_chart_of_mul_eq_of_agree (I : Ideal R) {W : Scheme.{u}}
    (h h' : W ⟶ Blowup.affineBlowup I) (𝔞 𝔟₁ : W.IdealSheafData) (a : I) (V : W.affineOpens)
    (hagree : 𝔞.subschemeι ≫ (h ≫ Blowup.AffineBlowup.toSpec I)
      = 𝔞.subschemeι ≫ (h' ≫ Blowup.AffineBlowup.toSpec I))
    (hpull : (Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I)
      = (Blowup.specIdealSheaf I).comap (h' ≫ Blowup.AffineBlowup.toSpec I))
    (hfac : (Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I) * 𝔟₁ = 𝔞)
    (hV : (V : W.Opens) ≤ (Opens.map h.base).obj
      ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤))
    (hV' : (V : W.Opens) ≤ (Opens.map h'.base).obj
      ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤))
    (hnzd : Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)
      ∈ nonZeroDivisors ↥(W.presheaf.obj (Opposite.op (V : W.Opens))))
    (hspan : ((Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I)).ideal V
      = Ideal.span {Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V : W.Opens) (a : R)}) :
    Scheme.Opens.ι ((Opens.map 𝔟₁.subschemeι.base).obj (V : W.Opens)) ≫ 𝔟₁.subschemeι ≫ h
      = Scheme.Opens.ι ((Opens.map 𝔟₁.subschemeι.base).obj (V : W.Opens)) ≫ 𝔟₁.subschemeι ≫ h' := by sorry
