-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_chartRingHom_mem_nonZeroDivisors
-- name    : FunctorialResolution.Blowup.chartRingHom_mem_nonZeroDivisors
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:39:48.06075+00:00
-- url     : https://prove2.me/theorems/62db72d7-ce64-4f51-954c-4d36bbe8ecb5
-- title:
--   Blowup: chart Ring Hom mem non Zero Divisors
-- statement:
--   The Blowup construction uses the chart Ring Hom mem non Zero Divisors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowup.lean#L201-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowup.lean#L201-L225

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

theorem FunctorialResolution.Blowup.chartRingHom_mem_nonZeroDivisors (I : Ideal R) (a : ↥I) :
    chartRingHom I a (a : R) ∈
      nonZeroDivisors (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) := by sorry
