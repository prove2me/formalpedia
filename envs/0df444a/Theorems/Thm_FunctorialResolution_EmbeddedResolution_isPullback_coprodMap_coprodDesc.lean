-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isPullback_coprodMap_coprodDesc
-- name    : FunctorialResolution.EmbeddedResolution.isPullback_coprodMap_coprodDesc
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:47:43.559798+00:00
-- url     : https://prove2.me/theorems/b9c30bf0-c213-4b51-93dc-44c7a503503e
-- title:
--   Embedded Resolution: is Pullback coprod Map coprod Desc
-- statement:
--   The Embedded Resolution construction uses the is Pullback coprod Map coprod Desc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/BinaryCoproductBaseChange.lean#L116-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/BinaryCoproductBaseChange.lean#L116-L146

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

theorem FunctorialResolution.EmbeddedResolution.isPullback_coprodMap_coprodDesc {X₁ X₂ P₁ P₂ Y Y' : Scheme.{u}}
    (a₁ : P₁ ⟶ X₁) (a₂ : P₂ ⟶ X₂) (b₁ : P₁ ⟶ Y') (b₂ : P₂ ⟶ Y')
    (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y) (u : Y' ⟶ Y)
    (h₁ : IsPullback a₁ b₁ f₁ u) (h₂ : IsPullback a₂ b₂ f₂ u) :
    IsPullback (coprod.map a₁ a₂) (coprod.desc b₁ b₂) (coprod.desc f₁ f₂) u := by sorry
