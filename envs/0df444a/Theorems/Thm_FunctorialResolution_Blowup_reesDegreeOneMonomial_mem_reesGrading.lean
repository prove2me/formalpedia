-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_reesDegreeOneMonomial_mem_reesGrading
-- name    : FunctorialResolution.Blowup.reesDegreeOneMonomial_mem_reesGrading
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:45:37.600093+00:00
-- url     : https://prove2.me/theorems/da08d1ee-8b36-43db-b155-22c10c0eaba6
-- title:
--   Blowup: rees Degree One Monomial mem rees Grading
-- statement:
--   The Blowup construction uses the rees Degree One Monomial mem rees Grading property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/ReesGrading.lean#L160-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/ReesGrading.lean#L160-L162

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

theorem FunctorialResolution.Blowup.reesDegreeOneMonomial_mem_reesGrading (I : Ideal R) {a : R} (ha : a ∈ I) :
    reesDegreeOneMonomial I a ha ∈ reesGrading I 1 := by sorry
