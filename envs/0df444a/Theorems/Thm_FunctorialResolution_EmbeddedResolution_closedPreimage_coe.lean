-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_closedPreimage_coe
-- name    : FunctorialResolution.EmbeddedResolution.closedPreimage_coe
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:46:54.681538+00:00
-- url     : https://prove2.me/theorems/c4e9d3a8-deac-4c16-b349-85084dd3b92c
-- title:
--   Embedded Resolution: closed Preimage coe
-- statement:
--   The Embedded Resolution construction uses the closed Preimage coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsOpenImmersion.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsOpenImmersion.lean#L19-L20

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

theorem FunctorialResolution.EmbeddedResolution.closedPreimage_coe {X X' : Scheme.{u}} (f : X' ⟶ X) (S : TopologicalSpace.Closeds X) :
    (closedPreimage f S : Set X') = f.base ⁻¹' (S : Set X) := by sorry
