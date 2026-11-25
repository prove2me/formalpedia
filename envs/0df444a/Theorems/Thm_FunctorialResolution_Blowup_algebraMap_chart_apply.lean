-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_algebraMap_chart_apply
-- name    : FunctorialResolution.Blowup.algebraMap_chart_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:52:37.802322+00:00
-- url     : https://prove2.me/theorems/142e7e11-dd3b-4a66-8e5a-9c1e3771b967
-- title:
--   Blowup: algebra Map chart apply
-- statement:
--   The Blowup construction uses the algebra Map chart apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowup.lean#L131-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowup.lean#L131-L134

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

theorem FunctorialResolution.Blowup.algebraMap_chart_apply (I : Ideal R) (a : ↥I) (r : R) :
    @algebraMap R (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) _ _
        (AffineBlowup.instAlgebraChart I a) r =
      chartRingHom I a r := by sorry
