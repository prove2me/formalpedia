-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isPullback_sigmaMap_sigmaDesc
-- name    : FunctorialResolution.EmbeddedResolution.isPullback_sigmaMap_sigmaDesc
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:47:44.187978+00:00
-- url     : https://prove2.me/theorems/8c41b6a4-091b-4543-ae3d-8b47ad743567
-- title:
--   Embedded Resolution: is Pullback sigma Map sigma Desc
-- statement:
--   The Embedded Resolution construction uses the is Pullback sigma Map sigma Desc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/CoproductBaseChange.lean#L37-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/CoproductBaseChange.lean#L37-L71

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_CoproductBaseChange
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

theorem FunctorialResolution.EmbeddedResolution.isPullback_sigmaMap_sigmaDesc {ι : Type u} [Finite ι] {A Y : Scheme.{u}} (i : Y ⟶ A)
    (B C : ι → Scheme.{u}) (j : ∀ a, C a ⟶ B a) (q : ∀ a, C a ⟶ Y) (h : ∀ a, B a ⟶ A)
    (hsq : ∀ a, IsPullback (j a) (q a) (h a) i) :
    IsPullback (Limits.Sigma.map j) (Limits.Sigma.desc q) (Limits.Sigma.desc h) i := by sorry
