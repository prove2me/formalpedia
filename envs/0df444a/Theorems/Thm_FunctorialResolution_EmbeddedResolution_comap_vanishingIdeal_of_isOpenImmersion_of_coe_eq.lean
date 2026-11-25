-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_comap_vanishingIdeal_of_isOpenImmersion_of_coe_eq
-- name    : FunctorialResolution.EmbeddedResolution.comap_vanishingIdeal_of_isOpenImmersion_of_coe_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:53:07.675612+00:00
-- url     : https://prove2.me/theorems/8a84826c-052f-4e42-a202-d6c5975ff6c9
-- title:
--   Embedded Resolution: comap vanishing Ideal of is Open Immersion of coe eq
-- statement:
--   The Embedded Resolution construction uses the comap vanishing Ideal of is Open Immersion of coe eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsOpenImmersion.lean#L123-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsOpenImmersion.lean#L123-L129

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

theorem FunctorialResolution.EmbeddedResolution.comap_vanishingIdeal_of_isOpenImmersion_of_coe_eq {X' Y' : Scheme.{u}} (h : X' ⟶ Y')
    [IsOpenImmersion h] (Z : TopologicalSpace.Closeds Y') (Z' : TopologicalSpace.Closeds X')
    (hZ' : (Z' : Set X') = h.base ⁻¹' (Z : Set Y')) :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap h
      = Scheme.IdealSheafData.vanishingIdeal Z' := by sorry
