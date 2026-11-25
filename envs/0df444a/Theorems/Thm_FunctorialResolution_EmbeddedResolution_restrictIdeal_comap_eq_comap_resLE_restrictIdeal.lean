-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_restrictIdeal_comap_eq_comap_resLE_restrictIdeal
-- name    : FunctorialResolution.EmbeddedResolution.restrictIdeal_comap_eq_comap_resLE_restrictIdeal
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:54:12.092509+00:00
-- url     : https://prove2.me/theorems/002fc1e4-c380-5eed-845c-5907846d2420
-- title:
--   Embedded Resolution: restrict Ideal comap eq comap res LE restrict Ideal
-- statement:
--   The Embedded Resolution construction uses the restrict Ideal comap eq comap res LE restrict Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossings.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossings.lean#L61-L66

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

theorem FunctorialResolution.EmbeddedResolution.restrictIdeal_comap_eq_comap_resLE_restrictIdeal {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U) :
    restrictIdeal (I.comap f) V = (restrictIdeal I U).comap (f.resLE U V h) := by sorry
