-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_algebraMap_mem_reesGrading_zero
-- name    : FunctorialResolution.Blowup.algebraMap_mem_reesGrading_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:52:36.671204+00:00
-- url     : https://prove2.me/theorems/ab7d2877-6a40-4f98-ae0b-439cd4dee8c3
-- title:
--   Blowup: algebra Map mem rees Grading zero
-- statement:
--   The Blowup construction uses the algebra Map mem rees Grading zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/ReesGrading.lean#L137-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/ReesGrading.lean#L137-L140

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

theorem FunctorialResolution.Blowup.algebraMap_mem_reesGrading_zero (I : Ideal R) (r : R) :
    algebraMap R ↥(reesAlgebra I) r ∈ reesGrading I 0 := by sorry
