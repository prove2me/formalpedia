-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_topologicalKrullDim_primeSpectrum_lt_top
-- name    : FunctorialResolution.EmbeddedResolution.topologicalKrullDim_primeSpectrum_lt_top
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:04:43.579565+00:00
-- url     : https://prove2.me/theorems/5449fd8d-1528-42a7-ac57-624c96158e83
-- title:
--   Embedded Resolution: topological Krull Dim prime Spectrum lt top
-- statement:
--   The Embedded Resolution construction uses the topological Krull Dim prime Spectrum lt top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/FiniteKrullDim.lean#L169-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/FiniteKrullDim.lean#L169-L172

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

theorem FunctorialResolution.EmbeddedResolution.topologicalKrullDim_primeSpectrum_lt_top (k : Type u) [Field k] (A : Type v) [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] : topologicalKrullDim (PrimeSpectrum A) < ⊤ := by sorry
