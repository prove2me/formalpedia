-- Prove2me | Theorems.Thm_Kyprianou_Ch01_geometricStoppedIIDCharFun
-- name    : Kyprianou.Ch01.geometricStoppedIIDCharFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:42:25.381993+00:00
-- url     : https://prove2.me/theorems/12ad2766-3edd-46c0-97cd-88819520dd6f
-- title:
--   Characteristic function of the strictly geometrically stopped IID real sum
-- statement:
--   For 0<p<1 and the full IID, common-law, geometric-count and independence hypotheses of Kyprianou Chapter 1 Exercise 1.2(ii), the characteristic function of the stopped sum equals p/[1−(1−p)φ_jumpLaw(ξ)] at all real frequencies. A complete derivation uses the independent-count conditional Fourier mixture, the fixed-count IID Fourier power and the convergent geometric series.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(ii), exact strict stopped IID random sum Fourier identity.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.geometricStoppedIIDCharFun
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (increment : ℕ → Ω → ℝ)
    (N : Ω → ℕ)
    (hNmeas : Measurable N)
    (hIncMeas : ∀ n : ℕ, Measurable (increment n))
    (hIID : iIndepFun increment P)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hCommon : ∀ n : ℕ,
      HasLaw (increment n) jumpLaw P)
    (hGeometric : ∀ k : ℕ,
      P {ω | N ω = k} =
        ENNReal.ofReal (p * (1 - p) ^ k))
    (hIndependent : IndepFun N
      (fun ω => fun n : ℕ => increment n ω) P) :
    ∀ xi : ℝ,
      charFun (P.map (fun ω =>
        ∑ i ∈ Finset.range (N ω), increment i ω)) xi =
        (p : ℂ) / (1 - (((1 - p : ℝ) : ℂ) * charFun jumpLaw xi)) := by
  sorry
