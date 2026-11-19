-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianUpperStoppedExponentialPointwiseLimitPublic
-- name    : Kyprianou.Ch01.brownianUpperStoppedExponentialPointwiseLimitPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T09:22:04.97688+00:00
-- url     : https://prove2.me/theorems/c6e665fe-0f53-4624-b4cb-ec877d457f7c
-- title:
--   Brownian upper passage: almost sure stopped exponential limit and payoff integrability
-- statement:
--   For Brownian motion satisfying the original Lévy law, positive discount, and strict positive upper level, the discounted first upper passage payoff is integrable and the capped positive adjustment-root exponential converges almost surely to exp(theta*x) times that payoff. On finite passage paths, use continuity and first passage contact; on infinite-passage paths use positive-discount exponential decay. Integrability follows from measurable stopping payoff and bound by one.
-- source:
--   Kyprianou (2006), Exercise 1.10(ii) worked solution, printed page 306.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianUpperStoppedExponentialPointwiseLimitPublic
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q x : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q) (hx : 0 < x)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    let theta : ℝ :=
      (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
    let F : ℕ → Ω → ℝ := fun N ω =>
      let T : ℝ≥0 := N
      let tauT : ℝ≥0 :=
        match firstUpperPassage X x ω with
        | none => T
        | some t => min t T
      Real.exp (theta * X tauT ω - q * (tauT : ℝ))
    Integrable (passageLaplace (firstUpperPassage X x) q) P ∧
    ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => F N ω) atTop
      (nhds (Real.exp (theta * x) *
        passageLaplace (firstUpperPassage X x) q ω)) := by sorry
