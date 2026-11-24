-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_iso_hom_comp_transitionMap
-- name    : FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.iso_hom_comp_transitionMap
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:47:08.576353+00:00
-- url     : https://prove2.me/theorems/708897d8-c55d-4b22-8751-62f3ff859f39
-- title:
--   Sequence Of Blowups: iso hom comp transition Map
-- statement:
--   The Sequence Of Blowups construction uses the iso hom comp transition Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/PullbackBlowupSequenceComposition.lean#L19-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/PullbackBlowupSequenceComposition.lean#L19-L38

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_SequenceIsomorphism
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PullbackBlowupSequenceComposition
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_Isomorphic_trans

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

theorem FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.iso_hom_comp_transitionMap {X : Scheme.{u}} (s t : SequenceOfBlowups X) (L : ℕ)
    (e : ∀ i : ℕ, i ≤ L → (s.schemeAt i ≅ t.schemeAt i))
    (hstep : ∀ i : ℕ, ∀ hi : i < L,
      (e (i + 1) hi).hom ≫ t.transitionMapSucc i = s.transitionMapSucc i ≫ (e i hi.le).hom) :
    ∀ a b : ℕ, ∀ hab : a ≤ b, ∀ hb : b ≤ L,
      (e b hb).hom ≫ t.transitionMap hab = s.transitionMap hab ≫ (e a (hab.trans hb)).hom := by sorry
