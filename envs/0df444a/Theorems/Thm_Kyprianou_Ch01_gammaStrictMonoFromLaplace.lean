-- Prove2me | Theorems.Thm_Kyprianou_Ch01_gammaStrictMonoFromLaplace
-- name    : Kyprianou.Ch01.gammaStrictMonoFromLaplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T19:40:59.071792+00:00
-- url     : https://prove2.me/theorems/856d65dc-1ba9-4cb1-b370-d033232e1953
-- title:
--   Gamma Lévy paths are strictly increasing from their Laplace semigroup
-- statement:
--   For any real-valued Lévy process whose nonnegative Laplace transforms at time t agree with the gamma convolution semigroup of positive shape beta*t and rate alpha, sample paths are almost surely strictly increasing on nonnegative time. Derivation requires no new distributional assumptions; use stationary independent increments, positivity of gamma increments, càdlàg paths and simultaneous rational-time arguments. This is the exact probabilistic component of the Chapter 1 gamma process path result.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.4, gamma process infinite activity and strictly increasing paths.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.gammaStrictMonoFromLaplace
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (alpha beta : ℝ) (hAlpha : 0 < alpha) (hBeta : 0 < beta)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hGammaLaplace : ∀ (t : ℝ≥0) (q : ℝ), 0 ≤ q →
      Integrable (fun ω => Real.exp (-q * X t ω)) P ∧
      (∫ ω, Real.exp (-q * X t ω) ∂P) =
        (alpha / (alpha + q)) ^ (beta * (t : ℝ))) :
    ∀ᵐ ω ∂P, StrictMono (fun t : ℝ≥0 => X t ω) := by sorry
