-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_LocalResolutionData_localSequence_center_eq_comap
-- name    : FunctorialResolution.EmbeddedResolution.LocalResolutionData.localSequence_center_eq_comap
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:46:06.59932+00:00
-- url     : https://prove2.me/theorems/70c9a670-3f4c-4aab-b530-23221bf32169
-- title:
--   Local Resolution Data: local Sequence center eq comap
-- statement:
--   The Local Resolution Data construction uses the local Sequence center eq comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/LocalResolutionData.lean#L95-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/LocalResolutionData.lean#L95-L101

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_StrongResolution
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_LocalResolutionData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
attribute [instance] LocalResolutionData.finiteType
open FunctorialResolution.EmbeddedResolution.LocalResolutionData
variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

theorem FunctorialResolution.EmbeddedResolution.LocalResolutionData.localSequence_center_eq_comap (d : LocalResolutionData k f s) (i : d.cover.I₀) (j : ℕ)
    (hj : j < (d.seq i).length) :
    (d.seq i).center j =
      (s.center (d.reindex i j)).comap
        ((d.schemeAtIsoPullback i j hj.le).hom ≫
          pullback.snd (d.cover.f i) (s.projectionToBase (d.reindex i j))) := by sorry
