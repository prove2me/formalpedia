-- Prove2me | Theorems.Thm_Kyprianou_Ch02_exercise27PiecewiseLinearV1
-- name    : Kyprianou.Ch02.exercise27PiecewiseLinearV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T23:12:40.926001+00:00
-- url     : https://prove2.me/theorems/18e6a86d-5a60-4b87-8286-5fb06c1ce0e3
-- title:
--   Piecewise affine paths iff finite activity and zero Gaussian coefficient
-- statement:
--   Use the finite-activity compound Poisson and drift representation, dense jumps for infinite activity, and the non-affinity of a nonzero Brownian component on every rational interval.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.7, exact projection of parent 38e63dd3-adcd-4a67-9720-963452efddea

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.exercise27PiecewiseLinearV1
    (a : ℝ) (σ : ℝ≥0) (ν : Measure ℝ)
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, ν, hν⟩ ξ))
    :
    let piecewiseLinear : (ℝ≥0 → ℝ) → Prop := fun f =>
      ∃ (T : ℕ → ℝ≥0), T 0 = 0 ∧ StrictMono T ∧
        Tendsto T atTop atTop ∧
        ∀ n : ℕ, ∃ (slope intercept : ℝ),
          ∀ t : ℝ≥0, T n ≤ t → t < T (n + 1) →
            f t = slope * (t : ℝ) + intercept
    ((∀ᵐ ω ∂P, piecewiseLinear (fun t => X t ω)) ↔
      σ = 0 ∧ ν Set.univ < ⊤) := by sorry
