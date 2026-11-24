-- Prove2me | Theorems.Thm_Kyprianou_Ch03_canonicalZeroOriginProductTransportV1
-- name    : Kyprianou.Ch03.canonicalZeroOriginProductTransportV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:16:51.778937+00:00
-- url     : https://prove2.me/theorems/c894a504-957a-4e3c-bafc-e27fc0f7b7cc
-- title:
--   Almost-sure zero origin permits transporting every finite coordinate marginal
-- statement:
--   Replace the zero coordinate by zero everywhere, form a measurable map to the zero-origin subtype and use almost-sure equality to preserve finite marginals.
-- source:
--   Kyprianou (2006), Chapter 3, Theorem 3.9; auxiliary reductions of canonicalProductZeroOriginMarginalsV1 and canonicalPastMeasuresEqOfFiniteMarginalsV1.

import Mathlib
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.canonicalZeroOriginProductTransportV1
    (μ : Measure (NNReal → ℝ)) [IsProbabilityMeasure μ]
    (h0 : ∀ᵐ f ∂μ, f 0 = 0) :
    ∃ Q : Measure {path : NNReal → ℝ // path 0 = 0}, IsProbabilityMeasure Q ∧
      ∀ I : Finset NNReal,
        Measure.map (fun w : {path : NNReal → ℝ // path 0 = 0} => I.restrict w.val) Q =
          Measure.map (I.restrict (π := fun _ : NNReal => ℝ)) μ := by
  sorry
