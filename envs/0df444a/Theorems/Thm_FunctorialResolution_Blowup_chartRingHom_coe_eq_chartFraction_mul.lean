-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_chartRingHom_coe_eq_chartFraction_mul
-- name    : FunctorialResolution.Blowup.chartRingHom_coe_eq_chartFraction_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:39:22.133999+00:00
-- url     : https://prove2.me/theorems/fa86ac52-5e96-4573-88b7-471112143ea1
-- title:
--   Blowup: chart Ring Hom coe eq chart Fraction mul
-- statement:
--   The Blowup construction uses the chart Ring Hom coe eq chart Fraction mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowup.lean#L181-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowup.lean#L181-L189

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

theorem FunctorialResolution.Blowup.chartRingHom_coe_eq_chartFraction_mul (I : Ideal R) (a b : ↥I) :
    chartRingHom I a (b : R) = chartFraction I a b * chartRingHom I a (a : R) := by sorry
