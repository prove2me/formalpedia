-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_ringKrullDim_lt_top_of_finiteType
-- name    : FunctorialResolution.EmbeddedResolution.ringKrullDim_lt_top_of_finiteType
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:04:24.862796+00:00
-- url     : https://prove2.me/theorems/8618dc53-6b22-43b2-bf89-de33ea5014de
-- title:
--   Embedded Resolution: ring Krull Dim lt top of finite Type
-- statement:
--   The Embedded Resolution construction uses the ring Krull Dim lt top of finite Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/FiniteKrullDim.lean#L162-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/FiniteKrullDim.lean#L162-L167

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

theorem FunctorialResolution.EmbeddedResolution.ringKrullDim_lt_top_of_finiteType (k : Type u) [Field k] (A : Type v) [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] : ringKrullDim A < ⊤ := by sorry
