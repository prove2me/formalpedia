-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_comap_homOfLE_restrictIdeal
-- name    : FunctorialResolution.EmbeddedResolution.restrictIdeal_eq_comap_homOfLE_restrictIdeal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:39:46.900391+00:00
-- url     : https://prove2.me/theorems/8b999ba7-a3b7-4840-952e-6a49b33c1b38
-- title:
--   Embedded Resolution: restrict Ideal eq comap hom Of LE restrict Ideal
-- statement:
--   The Embedded Resolution construction uses the restrict Ideal eq comap hom Of LE restrict Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossings.lean#L48-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossings.lean#L48-L53

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

theorem FunctorialResolution.EmbeddedResolution.restrictIdeal_eq_comap_homOfLE_restrictIdeal {X : Scheme.{u}} (I : X.IdealSheafData)
    {U V : X.Opens} (h : V ≤ U) :
    restrictIdeal I V = (restrictIdeal I U).comap (X.homOfLE h) := by sorry
