-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_exists_iso_pullback_coprod_desc_right
-- name    : FunctorialResolution.Blowup.exists_iso_pullback_coprod_desc_right
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:45:22.041729+00:00
-- url     : https://prove2.me/theorems/23b4ac94-c6b4-4ce6-8446-3d6251ef4fec
-- title:
--   Blowup: exists iso pullback coprod desc right
-- statement:
--   The Blowup construction uses the exists iso pullback coprod desc right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupCoproduct.lean#L553-L566
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupCoproduct.lean#L553-L566

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open FunctorialResolution FunctorialResolution.Blowup

theorem FunctorialResolution.Blowup.exists_iso_pullback_coprod_desc_right {X A F : Scheme.{u}} (f : A ⟶ X) (g : F ⟶ X)
    {U V : X.Opens} (h : IsCompl U V)
    (hf : Set.range ⇑f.base ⊆ Set.range ⇑U.ι.base)
    (hg : Set.range ⇑g.base ⊆ Set.range ⇑V.ι.base) :
    ∃ e : pullback (coprod.desc f g) V.ι ≅ F,
      e.hom ≫ IsOpenImmersion.lift V.ι g hg
          = pullback.snd (coprod.desc f g) V.ι ∧
        e.inv ≫ pullback.fst (coprod.desc f g) V.ι = (coprod.inr : F ⟶ A ⨿ F) := by sorry
