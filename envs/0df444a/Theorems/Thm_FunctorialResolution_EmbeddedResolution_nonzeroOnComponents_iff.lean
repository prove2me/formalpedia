-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_nonzeroOnComponents_iff
-- name    : FunctorialResolution.EmbeddedResolution.nonzeroOnComponents_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:01.692692+00:00
-- url     : https://prove2.me/theorems/01f4b872-e8a9-493b-8f2b-5e59a84e2642
-- title:
--   Embedded Resolution: nonzero On Components iff
-- statement:
--   The Embedded Resolution construction uses the nonzero On Components iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossings.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossings.lean#L82-L84

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.nonzeroOnComponents_iff {X : Scheme.{u}} (I : X.IdealSheafData) :
    NonzeroOnComponents I ↔ ∀ T ∈ irreducibleComponents (↥X), ¬ T ⊆ (I.support : Set ↥X) := by sorry
