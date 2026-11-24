-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_totalSpaceZeroIso_inv_eq
-- name    : FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.totalSpaceZeroIso_inv_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T14:53:24.089878+00:00
-- url     : https://prove2.me/theorems/0a733f27-50f8-4095-a62d-65b3dfd0fa3f
-- title:
--   Embedded Blowup Sequence: total Space Zero Iso inv eq
-- statement:
--   The Embedded Blowup Sequence construction uses the total Space Zero Iso inv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/StrictTransformTower.lean#L121-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/StrictTransformTower.lean#L121-L132

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

theorem FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.totalSpaceZeroIso_inv_eq :
    S.totalSpaceZeroIso.inv =
      S.strictTransformZeroIso.inv ≫ (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) := by sorry
