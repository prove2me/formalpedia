-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isPullback_initial_of_isEmpty
-- name    : FunctorialResolution.EmbeddedResolution.isPullback_initial_of_isEmpty
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:47:31.728433+00:00
-- url     : https://prove2.me/theorems/f8d81fdc-f678-4721-a8dc-58c5a41aef60
-- title:
--   Embedded Resolution: is Pullback initial of is Empty
-- statement:
--   The Embedded Resolution construction uses the is Pullback initial of is Empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/BinaryCoproductBaseChange.lean#L148-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/BinaryCoproductBaseChange.lean#L148-L156

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

theorem FunctorialResolution.EmbeddedResolution.isPullback_initial_of_isEmpty {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (u : Y' ⟶ Y)
    (h : ∀ (P : Scheme.{u}) (a : P ⟶ X) (b : P ⟶ Y'), a ≫ f = b ≫ u → IsEmpty P) :
    IsPullback (initial.to X) (initial.to Y') f u := by sorry
