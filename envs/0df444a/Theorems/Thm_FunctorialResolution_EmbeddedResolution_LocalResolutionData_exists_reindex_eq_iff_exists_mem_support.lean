-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_LocalResolutionData_exists_reindex_eq_iff_exists_mem_support
-- name    : FunctorialResolution.EmbeddedResolution.LocalResolutionData.exists_reindex_eq_iff_exists_mem_support
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:45:47.00571+00:00
-- url     : https://prove2.me/theorems/f47265b8-83e3-42e2-95e3-80ad38e34b26
-- title:
--   Local Resolution Data: exists reindex eq iff exists mem support
-- statement:
--   The Local Resolution Data construction uses the exists reindex eq iff exists mem support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/LocalResolutionData.lean#L103-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/LocalResolutionData.lean#L103-L106

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

theorem FunctorialResolution.EmbeddedResolution.LocalResolutionData.exists_reindex_eq_iff_exists_mem_support (d : LocalResolutionData k f s) (i : d.cover.I₀) (j : ℕ) (hj : j < s.length) :
    ((∃ l : ℕ, ∃ _ : l < (d.seq i).length, d.reindex i l = j) ↔
      ∃ x, x ∈ ((s.center j).comap (pullback.snd (d.cover.f i) (s.projectionToBase j))).support) := by sorry
