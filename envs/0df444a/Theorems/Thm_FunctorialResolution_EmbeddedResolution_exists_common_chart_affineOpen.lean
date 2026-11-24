-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_common_chart_affineOpen
-- name    : FunctorialResolution.EmbeddedResolution.exists_common_chart_affineOpen
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:24:45.213798+00:00
-- url     : https://prove2.me/theorems/8365b40b-945d-4dc1-8741-5a50e4e7a36a
-- title:
--   Embedded Resolution: exists common chart affine Open
-- statement:
--   The Embedded Resolution construction uses the exists common chart affine Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/BlowupChartCongruence.lean#L494-L585
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/BlowupChartCongruence.lean#L494-L585

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

theorem FunctorialResolution.EmbeddedResolution.exists_common_chart_affineOpen (I : Ideal R) {W : Scheme.{u}}
    (h h' : W ⟶ Blowup.affineBlowup I) (𝔞 𝔟₁ : W.IdealSheafData)
    (hagree : 𝔞.subschemeι ≫ (h ≫ Blowup.AffineBlowup.toSpec I)
      = 𝔞.subschemeι ≫ (h' ≫ Blowup.AffineBlowup.toSpec I))
    (hpull : (Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I)
      = (Blowup.specIdealSheaf I).comap (h' ≫ Blowup.AffineBlowup.toSpec I))
    (hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor ((Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I)))
    (hfac : (Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I) * 𝔟₁ = 𝔞)
    (w : ↥W) :
    ∃ (a : I) (V V' : W.affineOpens),
      w ∈ (V : W.Opens) ∧
      (Opens.map 𝔟₁.subschemeι.base).obj (V' : W.Opens)
        = (Opens.map 𝔟₁.subschemeι.base).obj (V : W.Opens) ∧
      (V' : W.Opens) ≤ (Opens.map h.base).obj
        ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤) ∧
      (V' : W.Opens) ≤ (Opens.map h'.base).obj
        ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤) ∧
      Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V' : W.Opens) (a : R)
        ∈ nonZeroDivisors ↥(W.presheaf.obj (Opposite.op (V' : W.Opens))) ∧
      ((Blowup.specIdealSheaf I).comap (h ≫ Blowup.AffineBlowup.toSpec I)).ideal V'
        = Ideal.span {Blowup.sectionsRingHom (h ≫ Blowup.AffineBlowup.toSpec I) (V' : W.Opens) (a : R)} := by sorry
