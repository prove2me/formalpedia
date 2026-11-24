-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_comp_eq_of_chartSectionsRingHom_sub_mem
-- name    : FunctorialResolution.EmbeddedResolution.comp_eq_of_chartSectionsRingHom_sub_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:24:55.637875+00:00
-- url     : https://prove2.me/theorems/b352799b-4aea-4df8-90e0-b9fb78c50b75
-- title:
--   Embedded Resolution: comp eq of chart Sections Ring Hom sub mem
-- statement:
--   The Embedded Resolution construction uses the comp eq of chart Sections Ring Hom sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/BlowupChartCongruence.lean#L331-L418
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/BlowupChartCongruence.lean#L331-L418

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

theorem FunctorialResolution.EmbeddedResolution.comp_eq_of_chartSectionsRingHom_sub_mem (I : Ideal R) {W : Scheme.{u}}
    (h h' : W ⟶ Blowup.affineBlowup I) (a : I) (𝔟 : W.IdealSheafData) (V : W.affineOpens)
    (hV : (V : W.Opens) ≤ (Opens.map h.base).obj
      ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤))
    (hV' : (V : W.Opens) ≤ (Opens.map h'.base).obj
      ((Scheme.Hom.opensFunctor (Blowup.affineBlowupChart I a)).obj ⊤))
    (hcongr : ∀ z : HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a),
      Blowup.chartSectionsRingHom I h a (V : W.Opens) hV z - Blowup.chartSectionsRingHom I h' a (V : W.Opens) hV' z
        ∈ 𝔟.ideal V) :
    Scheme.Opens.ι ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens)) ≫ 𝔟.subschemeι ≫ h
      = Scheme.Opens.ι ((Opens.map 𝔟.subschemeι.base).obj (V : W.Opens)) ≫ 𝔟.subschemeι ≫ h' := by sorry
