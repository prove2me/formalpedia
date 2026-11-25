-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isSmoothDivisor_top
-- name    : FunctorialResolution.EmbeddedResolution.isSmoothDivisor_top
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:58:26.118796+00:00
-- url     : https://prove2.me/theorems/dd849695-3a6e-41b3-a20d-9290c4252601
-- title:
--   Embedded Resolution: is Smooth Divisor top
-- statement:
--   The Embedded Resolution construction uses the is Smooth Divisor top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsWithoutUnitIdeals.lean#L234-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsWithoutUnitIdeals.lean#L234-L240

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsWithoutUnitIdeals
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k]

theorem FunctorialResolution.EmbeddedResolution.isSmoothDivisor_top (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] :
    IsSmoothDivisor p (⊤ : X.IdealSheafData) := by sorry
