-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_topologicalKrullDim_lt_top_of_finite_isOpenCover
-- name    : FunctorialResolution.EmbeddedResolution.topologicalKrullDim_lt_top_of_finite_isOpenCover
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:03:51.665798+00:00
-- url     : https://prove2.me/theorems/79f405a0-4666-46f6-89d7-c110dac29948
-- title:
--   Embedded Resolution: topological Krull Dim lt top of finite is Open Cover
-- statement:
--   The Embedded Resolution construction uses the topological Krull Dim lt top of finite is Open Cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/FiniteKrullDim.lean#L112-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/FiniteKrullDim.lean#L112-L123

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_KrullDimClosedSubset
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_FiniteKrullDim
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

theorem FunctorialResolution.EmbeddedResolution.topologicalKrullDim_lt_top_of_finite_isOpenCover {X : Type u} [TopologicalSpace X]
    {ι : Type v} [Finite ι] (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcov : ⋃ i, U i = Set.univ) (h : ∀ i, topologicalKrullDim ↥(U i) < ⊤) :
    topologicalKrullDim X < ⊤ := by sorry
