-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_reducedInverseImage_eq_vanishingIdeal_closedPreimage
-- name    : FunctorialResolution.EmbeddedResolution.reducedInverseImage_eq_vanishingIdeal_closedPreimage
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:47:02.175713+00:00
-- url     : https://prove2.me/theorems/59b00768-482a-4e60-a821-537f6b8b651e
-- title:
--   Embedded Resolution: reduced Inverse Image eq vanishing Ideal closed Preimage
-- statement:
--   The Embedded Resolution construction uses the reduced Inverse Image eq vanishing Ideal closed Preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsOpenImmersion.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsOpenImmersion.lean#L22-L24

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsOpenImmersion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.reducedInverseImage_eq_vanishingIdeal_closedPreimage {X X' : Scheme.{u}} (f : X' ⟶ X)
    (S : TopologicalSpace.Closeds X) :
    reducedInverseImage f S = Scheme.IdealSheafData.vanishingIdeal (closedPreimage f S) := by sorry
