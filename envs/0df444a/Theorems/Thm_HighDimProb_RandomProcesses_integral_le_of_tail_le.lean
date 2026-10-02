-- Prove2me | Theorems.Thm_HighDimProb_RandomProcesses_integral_le_of_tail_le
-- name    : HighDimProb.RandomProcesses.integral_le_of_tail_le
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-02T08:47:53.648174+00:00
-- url     : https://prove2.me/theorems/1baa4907-cafc-476f-b2ee-6567a6584caa
-- title:
--   Expectation comparison from all-threshold tail comparison
-- statement:
--   For integrable real random variables X and Y on a probability space, suppose that P(X ≥ t) ≤ P(Y ≥ t) for every real threshold t. Then E[X] ≤ E[Y]. Both variables may take negative values and may have atoms. The assumption covers all real thresholds. This supplies the expectation conclusion in finite Slepian once its probability comparison is established.
-- source:
--   Supporting consequence for Vershynin, High-Dimensional Probability, Theorem 7.2.9, derived from the layer-cake formula for the positive and negative parts. https://www.math.uci.edu/~rvershyn/papers/HDP-book/HDP-1.pdf. Mathlib MeasureTheory/Integral/Layercake.lean at revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
open MeasureTheory ProbabilityTheory

theorem HighDimProb.RandomProcesses.integral_le_of_tail_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : Integrable X P) (hY : Integrable Y P)
    (htail : ∀ t : ℝ, P.real {ω | t ≤ X ω} ≤ P.real {ω | t ≤ Y ω}) :
    (∫ ω, X ω ∂P) ≤ ∫ ω, Y ω ∂P := by sorry
