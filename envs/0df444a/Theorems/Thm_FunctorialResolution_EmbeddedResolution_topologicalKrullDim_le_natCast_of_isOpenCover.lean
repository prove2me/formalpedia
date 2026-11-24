-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_topologicalKrullDim_le_natCast_of_isOpenCover
-- name    : FunctorialResolution.EmbeddedResolution.topologicalKrullDim_le_natCast_of_isOpenCover
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:04:17.087911+00:00
-- url     : https://prove2.me/theorems/50830e53-05d4-4d78-834d-0fafc930a663
-- title:
--   Embedded Resolution: topological Krull Dim le nat Cast of is Open Cover
-- statement:
--   The Embedded Resolution construction uses the topological Krull Dim le nat Cast of is Open Cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/FiniteKrullDim.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/FiniteKrullDim.lean#L86-L90

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

theorem FunctorialResolution.EmbeddedResolution.topologicalKrullDim_le_natCast_of_isOpenCover {X : Type u} [TopologicalSpace X] {ι : Type v}
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ) (n : ℕ)
    (h : ∀ i, topologicalKrullDim ↥(U i) ≤ (n : WithBot ℕ∞)) :
    topologicalKrullDim X ≤ (n : WithBot ℕ∞) := by sorry
