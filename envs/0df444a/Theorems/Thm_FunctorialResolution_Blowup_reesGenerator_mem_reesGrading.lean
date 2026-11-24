-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_reesGenerator_mem_reesGrading
-- name    : FunctorialResolution.Blowup.reesGenerator_mem_reesGrading
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:48.51899+00:00
-- url     : https://prove2.me/theorems/bb2005c7-d05e-44b1-bdfc-be3138d352c8
-- title:
--   Blowup: rees Generator mem rees Grading
-- statement:
--   The Blowup construction uses the rees Generator mem rees Grading property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/ReesGrading.lean#L170-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/ReesGrading.lean#L170-L171

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

theorem FunctorialResolution.Blowup.reesGenerator_mem_reesGrading (I : Ideal R) (a : ↥I) : reesGenerator I a ∈ reesGrading I 1 := by sorry
