-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_reesGrading_irrelevant_le_span
-- name    : FunctorialResolution.Blowup.reesGrading_irrelevant_le_span
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:45:41.475111+00:00
-- url     : https://prove2.me/theorems/74826a71-5bc0-4966-a18e-25b75cf65da7
-- title:
--   Blowup: rees Grading irrelevant le span
-- statement:
--   The Blowup construction uses the rees Grading irrelevant le span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/ReesGrading.lean#L235-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/ReesGrading.lean#L235-L279

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

theorem FunctorialResolution.Blowup.reesGrading_irrelevant_le_span (I : Ideal R) :
    (HomogeneousIdeal.irrelevant (reesGrading I)).toIdeal ≤
      Ideal.span (Set.range (reesGenerator I)) := by sorry
