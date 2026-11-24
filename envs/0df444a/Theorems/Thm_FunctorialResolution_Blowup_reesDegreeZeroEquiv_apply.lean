-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_reesDegreeZeroEquiv_apply
-- name    : FunctorialResolution.Blowup.reesDegreeZeroEquiv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:25.53127+00:00
-- url     : https://prove2.me/theorems/e4c9ea56-0908-4337-a870-3482f40e6eab
-- title:
--   Blowup: rees Degree Zero Equiv apply
-- statement:
--   The Blowup construction uses the rees Degree Zero Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/ReesGrading.lean#L351-L352
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/ReesGrading.lean#L351-L352

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open FunctorialResolution FunctorialResolution.Blowup
variable {R : Type*} [CommRing R]

theorem FunctorialResolution.Blowup.reesDegreeZeroEquiv_apply (I : Ideal R) (r : R) :
    reesDegreeZeroEquiv I r = reesDegreeZeroRingHom I r := by sorry

attribute [defeq] FunctorialResolution.Blowup.reesDegreeZeroEquiv_apply
