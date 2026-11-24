-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_support_comap_subset_biUnion
-- name    : FunctorialResolution.EmbeddedResolution.support_comap_subset_biUnion
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:07:24.217387+00:00
-- url     : https://prove2.me/theorems/8716e303-f749-4edf-b934-092f14b067ec
-- title:
--   Embedded Resolution: support comap subset bi Union
-- statement:
--   The Embedded Resolution construction uses the support comap subset bi Union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MonomialCase/MonomialSplittingFlatPullback.lean#L27-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MonomialCase/MonomialSplittingFlatPullback.lean#L27-L35

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_CoordinateSubstitution
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IrreducibleComponentsOfSupport
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialPartAlongDivisor
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialSplitting
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialSplittingFlatPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X Y : Scheme.{u}}

theorem FunctorialResolution.EmbeddedResolution.support_comap_subset_biUnion (h : Y ⟶ X) (E : List X.IdealSheafData)
    (M : X.IdealSheafData) (hM : (M.support : Set X) ⊆ ⋃ D ∈ E, (D.support : Set X)) :
    ((M.comap h).support : Set Y) ⊆
      ⋃ D ∈ E.map (fun D : X.IdealSheafData => D.comap h), (D.support : Set Y) := by sorry
