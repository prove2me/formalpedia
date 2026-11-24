-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_comap_coordBlowupSubstMap_coordSubspaceIdeal_singleton_self
-- name    : FunctorialResolution.EmbeddedResolution.comap_coordBlowupSubstMap_coordSubspaceIdeal_singleton_self
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:46:31.195471+00:00
-- url     : https://prove2.me/theorems/788a4e34-2602-4b4f-9511-b44bf9136f70
-- title:
--   Embedded Resolution: comap coord Blowup Subst Map coord Subspace Ideal singleton self
-- statement:
--   The Embedded Resolution construction uses the comap coord Blowup Subst Map coord Subspace Ideal singleton self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/CoordinateSubstitution.lean#L95-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/CoordinateSubstitution.lean#L95-L99

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

theorem FunctorialResolution.EmbeddedResolution.comap_coordBlowupSubstMap_coordSubspaceIdeal_singleton_self (k : Type u) [Field k] (m : ℕ)
    (S : Finset (Fin m)) (s : Fin m) :
    (coordSubspaceIdeal k m {s}).comap (coordBlowupSubstMap k m S s) = coordSubspaceIdeal k m {s} := by sorry
