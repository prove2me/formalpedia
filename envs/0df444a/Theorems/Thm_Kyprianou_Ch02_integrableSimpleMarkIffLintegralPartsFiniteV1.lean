-- Prove2me | Theorems.Thm_Kyprianou_Ch02_integrableSimpleMarkIffLintegralPartsFiniteV1
-- name    : Kyprianou.Ch02.integrableSimpleMarkIffLintegralPartsFiniteV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T18:26:28.007373+00:00
-- url     : https://prove2.me/theorems/34fb5567-954a-460a-bf4c-e6783b021372
-- title:
--   Simple real marks integrable iff both signed lintegral parts are finite
-- statement:
--   Adapt the already Proved Kyprianou.Ch02.integrableMarkIffLintegralPartsFiniteV1 from identity mark z.2 to a real SimpleFunc mark f z.2, using f.measurable.comp measurable_snd, lintegral_ofReal_ne_top_iff_integrable, Integrable.pos_part and neg_part. Needed to prove signed simple-mark PRM measurability and Eq. 2.3.
-- source:
--   Kyprianou (2006) Chapter 2, signed finite activity integrability.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.integrableSimpleMarkIffLintegralPartsFiniteV1
    (μ : Measure (ℝ × ℝ)) (R : Set (ℝ × ℝ))
    (hR : MeasurableSet R) (f : SimpleFunc ℝ ℝ) :
    Integrable (fun z : ℝ × ℝ => f z.2) (μ.restrict R) ↔
      (∫⁻ z in R, ENNReal.ofReal (f z.2) ∂μ) ≠ ⊤ ∧
      (∫⁻ z in R, ENNReal.ofReal (-(f z.2)) ∂μ) ≠ ⊤ := by sorry
