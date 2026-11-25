-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isPullback_comp_inl_coprodDesc
-- name    : FunctorialResolution.EmbeddedResolution.isPullback_comp_inl_coprodDesc
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:57:41.336077+00:00
-- url     : https://prove2.me/theorems/e18b2c01-0f63-533b-8e7b-5ba3ac2ebdf2
-- title:
--   Embedded Resolution: is Pullback comp inl coprod Desc
-- statement:
--   The Embedded Resolution construction uses the is Pullback comp inl coprod Desc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/BinaryCoproductBaseChange.lean#L158-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/BinaryCoproductBaseChange.lean#L158-L173

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_CoproductBaseChange
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_BinaryCoproductBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.isPullback_comp_inl_coprodDesc {P X Y Y' F : Scheme.{u}}
    (a : P ⟶ X) (b : P ⟶ Y') (q : X ⟶ Y) (u : Y' ⟶ Y) (r : F ⟶ Y)
    (hsq : IsPullback a b q u)
    (hF : ∀ (Q : Scheme.{u}) (c : Q ⟶ F) (d : Q ⟶ Y'), c ≫ r = d ≫ u → IsEmpty Q) :
    IsPullback (a ≫ coprod.inl) b (coprod.desc q r) u := by sorry
