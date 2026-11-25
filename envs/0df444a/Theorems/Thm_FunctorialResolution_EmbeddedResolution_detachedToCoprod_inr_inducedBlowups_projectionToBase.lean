-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_detachedToCoprod_inr_inducedBlowups_projectionToBase
-- name    : FunctorialResolution.EmbeddedResolution.detachedToCoprod_inr_inducedBlowups_projectionToBase
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:53:30.966066+00:00
-- url     : https://prove2.me/theorems/c015ee15-1a03-52ef-be6c-56ae99f9777e
-- title:
--   Embedded Resolution: detached To Coprod inr induced Blowups projection To Base
-- statement:
--   The Embedded Resolution construction uses the detached To Coprod inr induced Blowups projection To Base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/StrictTransformTower.lean#L439-L464
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/StrictTransformTower.lean#L439-L464

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedStrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_StrictTransformTower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]

theorem FunctorialResolution.EmbeddedResolution.detachedToCoprod_inr_inducedBlowups_projectionToBase (S : EmbeddedBlowupSequence k Y pY) (h : S.TransitionsAreBlowups)
    (s i : ℕ) (hs : s < i) :
    S.detachedToCoprod s i hs ≫ (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) ≫
        (S.inducedBlowups h).projectionToBase i =
      S.detachedι s ≫ S.strictTransformToBase s := by sorry
