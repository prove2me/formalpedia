-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_appLE_top_comp_topIso_inv
-- name    : FunctorialResolution.EmbeddedResolution.appLE_top_comp_topIso_inv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:16:46.76113+00:00
-- url     : https://prove2.me/theorems/57642706-ff3a-46e3-84d2-cee4932a09b1
-- title:
--   Embedded Resolution: app LE top comp top Iso inv
-- statement:
--   The Embedded Resolution construction uses the app LE top comp top Iso inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/ChartRing.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/ChartRing.lean#L30-L33

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.appLE_top_comp_topIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y) (V : X.Opens)
    (hV : V ≤ f ⁻¹ᵁ (⊤ : Y.Opens)) :
    f.appLE ⊤ V hV ≫ V.topIso.inv = (V.ι ≫ f).appTop := by sorry
