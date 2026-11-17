-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianPassageHalfStableLevyProcessZeroBoundaryV2
-- name    : Kyprianou.Ch01.brownianPassageHalfStableLevyProcessZeroBoundaryV2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T23:29:39.770048+00:00
-- url     : https://prove2.me/theorems/c00d1109-b567-498d-abaa-d7e6077b53ed
-- title:
--   Exercise 1.7: the full first-passage time process is an index-one-half stable subordinator (pathwise zero-level boundary repaired)
-- statement:
--   The complete Exercise 1.7 (Kyprianou p. 29): the first-passage process τ_s=inf{t≥0:B_t≥s} of standard driftless Brownian motion is a Lévy subordinator, with stationary independent increments, a.s. finite passage times, and Laplace exponent √(2q). This identifies its strict 1/2-stable law with positivity/skewness parameter β=1, strengthening the existing one-time passage-transform draft. Continuity is assumed for the chosen sample-path version; none of the Lévy-process or stable Laplace identities is assumed. The level-zero passage time is explicitly set to zero for every sample path; for all strictly positive levels the original firstUpperPassage definition is unchanged. This removes the pathwise-start-zero counterexample identified by the moderator without adding hypotheses.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.7, printed p. 29.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators
open scoped Classical
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianPassageHalfStableLevyProcessZeroBoundaryV2
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ)
    (hB : Kyprianou.Ch01.IsLinearBrownian P B 1 0)
    (hMeas : ∀ t : ℝ≥0, Measurable (B t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => B t ω)) :
    let T : ℝ≥0 → Ω → ℝ :=
      fun s ω =>
        if s = 0 then (0 : ℝ)
        else (match Kyprianou.Ch01.firstUpperPassage B (s : ℝ) ω with
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
