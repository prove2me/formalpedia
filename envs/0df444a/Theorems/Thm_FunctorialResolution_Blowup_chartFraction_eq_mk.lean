-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_chartFraction_eq_mk
-- name    : FunctorialResolution.Blowup.chartFraction_eq_mk
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:40:22.236+00:00
-- url     : https://prove2.me/theorems/bf14775e-de39-4b64-a021-f128750577d6
-- title:
--   Blowup: chart Fraction eq mk
-- statement:
--   The Blowup construction uses the chart Fraction eq mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowup.lean#L173-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowup.lean#L173-L179

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Theorems.Thm_FunctorialResolution_Blowup_reesGenerator_mem_reesGrading

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

theorem FunctorialResolution.Blowup.chartFraction_eq_mk (I : Ideal R) (a b : ↥I) :
    chartFraction I a b =
      HomogeneousLocalization.mk
        { deg := 1
          num := ⟨reesGenerator I b, reesGenerator_mem_reesGrading I b⟩
          den := ⟨reesGenerator I a ^ 1, reesGenerator_pow_one_mem_reesGrading_one I a⟩
          den_mem := reesGenerator_pow_one_mem_powers I a } := by sorry
