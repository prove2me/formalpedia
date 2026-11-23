-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteMarkTimeRectIntensityFiniteV1
-- name    : Kyprianou.Ch02.prmFiniteMarkTimeRectIntensityFiniteV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T14:11:54.645947+00:00
-- url     : https://prove2.me/theorems/60b51af8-9387-45f9-9c2b-7592173434bc
-- title:
--   Finite mark intensity gives finite PRM reference intensity on every bounded nonnegative time interval
-- statement:
--   For any NNReal times a,b and a finite-measure measurable mark set B, the KLS reference Poisson intensity of (a,b]×B is finite. Evaluate referenceIntensity as a product of Lebesgue volume and ν B using Measure.prod_prod, Measure.restrict_apply, Real.volume_Ioc, and monotonicity of the nonnegative lower endpoint; then use ENNReal.mul_ne_top and ENNReal.ofReal_ne_top. This lemma lets the accepted Poisson integer-valued restriction theorem be applied to arbitrary finite shifted and original windows, closing the window integrability input for Eq. (2.3).
-- source:
--   Kyprianou (2006) Chapter 2 Eq. (2.3) finite-activity Poisson random measure.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteMarkTimeRectIntensityFiniteV1
    (ν : Measure ℝ) [SigmaFinite ν]
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (a b : ℝ≥0) :
    LevyStochCalc.Poisson.referenceIntensity ν
      (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ B) ≠ ⊤ := by sorry
