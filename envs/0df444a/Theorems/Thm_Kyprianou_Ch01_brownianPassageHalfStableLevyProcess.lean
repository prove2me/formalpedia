-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianPassageHalfStableLevyProcess
-- name    : Kyprianou.Ch01.brownianPassageHalfStableLevyProcess
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T08:21:49.629964+00:00
-- url     : https://prove2.me/theorems/71200432-a7b7-4caf-8fda-1705f63f63cb
-- title:
--   Exercise 1.7: the full first-passage time process is an index-one-half stable subordinator
-- statement:
--   The complete Exercise 1.7 (Kyprianou p. 29): the first-passage process τ_s=inf{t≥0:B_t≥s} of standard driftless Brownian motion is a Lévy subordinator, with stationary independent increments, a.s. finite passage times, and Laplace exponent √(2q). This identifies its strict 1/2-stable law with positivity/skewness parameter β=1, strengthening the existing one-time passage-transform draft. Continuity is assumed for the chosen sample-path version; none of the Lévy-process or stable Laplace identities is assumed.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.7, printed p. 29.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianPassageHalfStableLevyProcess
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ)
    (hB : Kyprianou.Ch01.IsLinearBrownian P B 1 0)
    (hMeas : ∀ t : ℝ≥0, Measurable (B t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => B t ω)) :
    let T : ℝ≥0 → Ω → ℝ :=
      fun s ω =>
        (match Kyprianou.Ch01.firstUpperPassage B (s : ℝ) ω with
        | none => (0 : ℝ)
        | some t => (t : ℝ))
    (∀ s : ℝ≥0, 0 < s →
      ∀ᵐ ω ∂P,
        Kyprianou.Ch01.firstUpperPassage B (s : ℝ) ω ≠ ⊤) ∧
    ProbabilityTheory.IsLevyProcess T P ∧
    (∀ (s : ℝ≥0) (q : ℝ), 0 < s → 0 ≤ q →
      Integrable (fun ω => Real.exp (-q * T s ω)) P ∧
      (∫ ω, Real.exp (-q * T s ω) ∂P) =
        Real.exp (-(s : ℝ) * Real.sqrt (2 * q))) := by
  sorry
