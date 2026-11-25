-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_detachedToCoprod_detachedCoprodMapOfLE
-- name    : FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.detachedToCoprod_detachedCoprodMapOfLE
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:52:59.5205+00:00
-- url     : https://prove2.me/theorems/a2e015be-198e-5ea0-be61-ab5cec8882a1
-- title:
--   Embedded Blowup Sequence: detached To Coprod detached Coprod Map Of LE
-- statement:
--   The Embedded Blowup Sequence construction uses the detached To Coprod detached Coprod Map Of LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/StrictTransformTower.lean#L338-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/StrictTransformTower.lean#L338-L358

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
open FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
variable (S : EmbeddedBlowupSequence k Y pY)

theorem FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.detachedToCoprod_detachedCoprodMapOfLE {s a b : ℕ} (hsa : s < a) (hab : a ≤ b) :
    S.detachedToCoprod s a hsa ≫ S.detachedCoprodMapOfLE hab = S.detachedToCoprod s b (lt_of_lt_of_le hsa hab) := by sorry
