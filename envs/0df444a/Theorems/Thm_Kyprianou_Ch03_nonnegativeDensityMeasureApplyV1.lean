-- Prove2me | Theorems.Thm_Kyprianou_Ch03_nonnegativeDensityMeasureApplyV1
-- name    : Kyprianou.Ch03.nonnegativeDensityMeasureApplyV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:03:21.44175+00:00
-- url     : https://prove2.me/theorems/0e500933-5a60-4cee-8dfa-c94472413d70
-- title:
--   Nonnegative integrable density evaluates measurable sets by indicator integrals
-- statement:
--   Apply the density evaluation formula on a measurable set and the equality between the nonnegative Bochner integral and the lower integral.
-- source:
--   Kyprianou (2006), Chapter 3, Theorem 3.9; decomposition of ce5a93d8-17ee-412f-a624-8c24a6d7a941

import Mathlib
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.nonnegativeDensityMeasureApplyV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ) (hf : Integrable f P) (hn : ∀ w, 0 ≤ f w)
    (A : Set Ω) (hA : MeasurableSet A) :
    (P.withDensity (fun w => ENNReal.ofReal (f w))) A =
      ENNReal.ofReal (∫ w, Set.indicator A f w ∂P) := by sorry
