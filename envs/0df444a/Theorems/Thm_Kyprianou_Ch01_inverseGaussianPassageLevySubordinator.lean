-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianPassageLevySubordinator
-- name    : Kyprianou.Ch01.inverseGaussianPassageLevySubordinator
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T08:11:43.109318+00:00
-- url     : https://prove2.me/theorems/9486a5d0-6de9-4840-be7b-e67a7438e793
-- title:
--   §1.2.5: inverse Gaussian Brownian first-passage process is a Lévy subordinator
-- statement:
--   Kyprianou (2006), Chapter 1 §1.2.5, printed pp. 8–9, equation (1.4): the first-passage time process τ_s=inf{t>0:B_t+bt>s} of a standard Brownian motion with positive drift b is a Lévy subordinator. Prove almost-sure finiteness of positive-level passage, stationary independent increments and Lévy regularity of the level-indexed process, plus its inverse Gaussian Laplace exponent √(b²+2q)−b. This strengthens the prior scalar inverse Gaussian transform to the whole process; its properties are not among the assumptions.
-- source:
--   Kyprianou (2006), Chapter 1, §1.2.5, printed pp. 8–9, equation (1.4) and surrounding construction.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianPassageLevySubordinator
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (b : ℝ) (hb : 0 < b)
    (hB : Kyprianou.Ch01.IsLinearBrownian P X 1 b)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) :
    let T : ℝ≥0 → Ω → ℝ :=
      fun s ω =>
        (match Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω with
        | none => (0 : ℝ)
        | some t => (t : ℝ))
    (∀ s : ℝ≥0, 0 < s →
      ∀ᵐ ω ∂P,
        Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω ≠ ⊤) ∧
      ProbabilityTheory.IsLevyProcess T P ∧
      (∀ (s : ℝ≥0) (q : ℝ), 0 < s → 0 ≤ q →
        Integrable (fun ω => Real.exp (-q * T s ω)) P ∧
        (∫ ω, Real.exp (-q * T s ω) ∂P) =
          Real.exp (-(s : ℝ) *
            (Real.sqrt (b ^ 2 + 2 * q) - b))) := by
  sorry
