-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_support_centerOffDetached_subset_preimage
-- name    : FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.support_centerOffDetached_subset_preimage
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:53:19.739314+00:00
-- url     : https://prove2.me/theorems/3eeae7b3-ef74-566a-9280-20b774216ec0
-- title:
--   Embedded Blowup Sequence: support center Off Detached subset preimage
-- statement:
--   The Embedded Blowup Sequence construction uses the support center Off Detached subset preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/StrictTransformTower.lean#L380-L400
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/StrictTransformTower.lean#L380-L400

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

theorem FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.support_centerOffDetached_subset_preimage (i : ℕ) :
    ((S.centerOffDetached i).support : Set ↥(S.strictTransform i)) ⊆
      ⇑(S.strictTransformι i).base ⁻¹' ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) := by sorry
