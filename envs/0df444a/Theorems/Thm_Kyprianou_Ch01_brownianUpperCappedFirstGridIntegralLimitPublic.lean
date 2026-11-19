-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianUpperCappedFirstGridIntegralLimitPublic
-- name    : Kyprianou.Ch01.brownianUpperCappedFirstGridIntegralLimitPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T10:02:08.160166+00:00
-- url     : https://prove2.me/theorems/90dfe54a-5723-4768-b3b4-f876c064b90a
-- title:
--   Brownian upper passage capped-grid martingale expectations converge to the continuous stopped value
-- statement:
--   The compensated Brownian exponentials stopped at first upper crossing on successively finer capped grids have expectations converging to the expectation at the actual continuous first strict upper passage or T, and this continuous stopped payoff is integrable. The proof requires almost-sure convergence of grid first passage times, first-contact continuity, and uniform integrability furnished by the fixed-physical-horizon L2 bound.
-- source:
--   Kyprianou (2006), Exercise 1.10(ii), back-of-book proof using stopped exponential and first-passage approximation, printed page 306.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianUpperCappedFirstGridIntegralLimitPublic
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q x : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q) (hx : 0 < x)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (T : ℝ≥0) :
    let theta : ℝ :=
      (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
    let G : ℕ → Ω → ℝ := fun N ω =>
      let K : ℕ := N + 1
      let delta : ℝ≥0 := T / (K : ℝ≥0)
      let tau : Ω → ℕ := fun ξ => by
        classical
        exact Nat.find (show ∃ k : ℕ,
          k = K ∨ x < X ((k : ℝ≥0) * delta) ξ from ⟨K, Or.inl rfl⟩)
      Real.exp (theta * X ((tau ω : ℝ≥0) * delta) ω -
        q * (((tau ω : ℝ≥0) * delta) : ℝ))
    let tauT : Ω → ℝ≥0 := fun ω =>
      match firstUpperPassage X x ω with
      | none => T
      | some t => min t T
    Integrable (fun ω => Real.exp (theta * X (tauT ω) ω -
      q * (tauT ω : ℝ))) P ∧
    Tendsto (fun N : ℕ => ∫ ω, G N ω ∂P) atTop
      (nhds (∫ ω, Real.exp (theta * X (tauT ω) ω -
        q * (tauT ω : ℝ)) ∂P)) := by sorry
