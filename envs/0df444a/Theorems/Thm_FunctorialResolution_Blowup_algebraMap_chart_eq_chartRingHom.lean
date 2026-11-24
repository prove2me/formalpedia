-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_algebraMap_chart_eq_chartRingHom
-- name    : FunctorialResolution.Blowup.algebraMap_chart_eq_chartRingHom
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:39:35.648811+00:00
-- url     : https://prove2.me/theorems/3c58a1d9-e223-4de0-beaa-63213d154736
-- title:
--   Blowup: algebra Map chart eq chart Ring Hom
-- statement:
--   The Blowup construction uses the algebra Map chart eq chart Ring Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowup.lean#L126-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowup.lean#L126-L129

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

theorem FunctorialResolution.Blowup.algebraMap_chart_eq_chartRingHom (I : Ideal R) (a : ↥I) :
    @algebraMap R (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) _ _
        (AffineBlowup.instAlgebraChart I a) =
      chartRingHom I a := by sorry
