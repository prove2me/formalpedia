-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_topologicalKrullDim_lt_of_isClosed_of_not_subset_irreducibleComponents
-- name    : FunctorialResolution.EmbeddedResolution.topologicalKrullDim_lt_of_isClosed_of_not_subset_irreducibleComponents
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:47:48.509801+00:00
-- url     : https://prove2.me/theorems/ef77a0f6-9f4e-418c-b141-48d14cfa3d7e
-- title:
--   Embedded Resolution: topological Krull Dim lt of is Closed of not subset irreducible Components
-- statement:
--   The Embedded Resolution construction uses the topological Krull Dim lt of is Closed of not subset irreducible Components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/KrullDimClosedSubset.lean#L56-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/KrullDimClosedSubset.lean#L56-L123

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_KrullDimClosedSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open TopologicalSpace AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open Order

theorem FunctorialResolution.EmbeddedResolution.topologicalKrullDim_lt_of_isClosed_of_not_subset_irreducibleComponents
    {X : Type u} [TopologicalSpace X] (Y : Set X) (hY : IsClosed Y) (hne : Y.Nonempty)
    (hcomp : ∀ C ∈ irreducibleComponents X, ¬ C ⊆ Y)
    (hfin : topologicalKrullDim X < ⊤) :
    topologicalKrullDim ↥Y < topologicalKrullDim X := by sorry
