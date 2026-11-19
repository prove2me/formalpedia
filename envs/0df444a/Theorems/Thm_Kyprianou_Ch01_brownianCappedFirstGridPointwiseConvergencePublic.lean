-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianCappedFirstGridPointwiseConvergencePublic
-- name    : Kyprianou.Ch01.brownianCappedFirstGridPointwiseConvergencePublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T12:19:50.412018+00:00
-- url     : https://prove2.me/theorems/c30c5ab6-86cb-4812-bd32-9bdd7419dece
-- title:
--   Fine capped upper first-crossing Brownian grids converge pathwise to the true stopped exponential
-- statement:
--   For almost every continuous Brownian path, its compensated adjustment-root exponential evaluated at the earliest strict upper-crossing point of successively finer physical grids of [0,T] converges to the same exponential at the genuine continuous first upper-passage time capped by T. The grid retains the terminal sentinel and uses K=N+1; continuity, the infimum property and detection of strict-crossing neighbourhoods underpin the result.
-- source:
--   Kyprianou (2006), Exercise 1.10(ii), back-of-book continuous first-passage and finite-grid approximation.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianCappedFirstGridPointwiseConvergencePublic
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
    ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => G N ω) atTop
      (nhds (Real.exp (theta * X (tauT ω) ω - q * (tauT ω : ℝ)))) := by sorry
