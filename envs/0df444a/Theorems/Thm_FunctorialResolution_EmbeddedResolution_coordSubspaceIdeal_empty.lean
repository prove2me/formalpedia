-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordSubspaceIdeal_empty
-- name    : FunctorialResolution.EmbeddedResolution.coordSubspaceIdeal_empty
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:52:48.451067+00:00
-- url     : https://prove2.me/theorems/181e7566-8cc5-5103-8fbd-9422e075b01d
-- title:
--   Embedded Resolution: coord Subspace Ideal empty
-- statement:
--   The Embedded Resolution construction uses the coord Subspace Ideal empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/CoordinateSubstitution.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/CoordinateSubstitution.lean#L14-L19

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_CoordinateSubstitution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.coordSubspaceIdeal_empty (k : Type u) [Field k] (m : ℕ) :
    coordSubspaceIdeal k m (∅ : Finset (Fin m)) = ⊥ := by sorry
