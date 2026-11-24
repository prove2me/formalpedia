-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_chartRingHom_apply
-- name    : FunctorialResolution.Blowup.chartRingHom_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:39:36.576478+00:00
-- url     : https://prove2.me/theorems/0bddc67b-4972-40c5-80b8-687febca77ad
-- title:
--   Blowup: chart Ring Hom apply
-- statement:
--   The Blowup construction uses the chart Ring Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowup.lean#L112-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowup.lean#L112-L115

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.Blowup
universe u
variable {R : Type u} [CommRing R]

theorem FunctorialResolution.Blowup.chartRingHom_apply (I : Ideal R) (a : ↥I) (r : R) :
    chartRingHom I a r =
      HomogeneousLocalization.fromZeroRingHom (reesGrading I) (Submonoid.powers (reesGenerator I a))
        (reesDegreeZeroEquiv I r) := by sorry
