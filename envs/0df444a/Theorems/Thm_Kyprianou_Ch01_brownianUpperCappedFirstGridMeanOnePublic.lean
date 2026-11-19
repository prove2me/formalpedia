-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianUpperCappedFirstGridMeanOnePublic
-- name    : Kyprianou.Ch01.brownianUpperCappedFirstGridMeanOnePublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T10:02:20.142789+00:00
-- url     : https://prove2.me/theorems/3057c0db-1635-45fa-9866-0d90a0470114
-- title:
--   Brownian upper passage capped-first-crossing grid stopped exponential has expected value one for each mesh
-- statement:
--   For each integer N, take the positive physical grid T/(N+1), stop at its first strict upper crossing before the sentinel K=N+1, or at the sentinel. Under the original Brownian process law the compensated adjustment-root exponential is integrable and has mean exactly one. This uses eventwise measurable grid continuation and the public finite-grid optional stopping theorem.
-- source:
--   Kyprianou (2006), Exercise 1.10(ii), back-of-book proof using stopped exponential and first-passage approximation, printed page 306.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianUpperCappedFirstGridMeanOnePublic
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
    ∀ N : ℕ, Integrable (G N) P ∧ (∫ ω, G N ω ∂P) = 1 := by sorry
