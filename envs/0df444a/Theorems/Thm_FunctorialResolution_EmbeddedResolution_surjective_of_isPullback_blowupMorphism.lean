-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_surjective_of_isPullback_blowupMorphism
-- name    : FunctorialResolution.EmbeddedResolution.surjective_of_isPullback_blowupMorphism
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:49:14.392811+00:00
-- url     : https://prove2.me/theorems/35fcb3ea-326b-45d1-9d8b-f93a30e6a9c6
-- title:
--   Embedded Resolution: surjective of is Pullback blowup Morphism
-- statement:
--   The Embedded Resolution construction uses the surjective of is Pullback blowup Morphism property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/PullbackBlowupSequenceComposition.lean#L93-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/PullbackBlowupSequenceComposition.lean#L93-L105

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_SequenceIsomorphism
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PullbackBlowupSequenceComposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.surjective_of_isPullback_blowupMorphism {X' X : Scheme.{u}} (g : X' ⟶ X)
    [AlgebraicGeometry.Surjective g]
    (t : SequenceOfBlowups X') (s : SequenceOfBlowups X) (L : ℕ)
    (σ : ∀ i : ℕ, i ≤ L → (t.schemeAt i ⟶ s.schemeAt i))
    (hzero : σ 0 (Nat.zero_le _) ≫ s.isoZero.hom = t.isoZero.hom ≫ g)
    (hstep : ∀ i : ℕ, ∀ hi : i < L,
      IsPullback (σ (i + 1) hi) (t.transitionMapSucc i) (s.transitionMapSucc i) (σ i hi.le)) :
    ∀ i : ℕ, ∀ hi : i ≤ L, AlgebraicGeometry.Surjective (σ i hi) := by sorry
