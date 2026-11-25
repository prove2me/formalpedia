-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_zeroLocus_eq_support
-- name    : FunctorialResolution.EmbeddedResolution.zeroLocus_eq_support
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:55:02.117037+00:00
-- url     : https://prove2.me/theorems/8186197c-2fd2-4a07-a3b2-880fdcdb1d7c
-- title:
--   Embedded Resolution: zero Locus eq support
-- statement:
--   The Embedded Resolution construction uses the zero Locus eq support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossings.lean#L71-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossings.lean#L71-L72

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

theorem FunctorialResolution.EmbeddedResolution.zeroLocus_eq_support {X : Scheme.{u}} (I : X.IdealSheafData) :
    zeroLocus I = I.support := by sorry
