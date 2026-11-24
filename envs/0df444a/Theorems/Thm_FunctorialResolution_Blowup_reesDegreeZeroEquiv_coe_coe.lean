-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_reesDegreeZeroEquiv_coe_coe
-- name    : FunctorialResolution.Blowup.reesDegreeZeroEquiv_coe_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:46.724142+00:00
-- url     : https://prove2.me/theorems/524dfeeb-72a1-4de2-b184-3894b74a8eea
-- title:
--   Blowup: rees Degree Zero Equiv coe coe
-- statement:
--   The Blowup construction uses the rees Degree Zero Equiv coe coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/ReesGrading.lean#L354-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/ReesGrading.lean#L354-L356

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

theorem FunctorialResolution.Blowup.reesDegreeZeroEquiv_coe_coe (I : Ideal R) (r : R) :
    ((reesDegreeZeroEquiv I r : ↥(reesAlgebra I)) : R[X]) = Polynomial.C r := by sorry
