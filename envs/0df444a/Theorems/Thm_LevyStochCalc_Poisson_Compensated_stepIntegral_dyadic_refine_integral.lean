-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_stepIntegral_dyadic_refine_integral
-- name    : LevyStochCalc.Poisson.Compensated.stepIntegral_dyadic_refine_integral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T09:22:56.849789+00:00
-- url     : https://prove2.me/theorems/60a41110-6807-43bb-83ec-0820147d9891
-- title:
--   stepIntegral dyadic refine integral
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.stepIntegral_dyadic_refine_integral` is extracted from `LevyStochCalc.Poisson.CompensatedDensityRefinement`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRefinement_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Doob `L²` bricks and dyadic cross-resolution refinement

Two preparations for the passage to the limit: the submartingale property of `‖M‖` and the
discrete tail maximal inequality for a martingale, and the re-expression of a dyadic step
integrand at level `n` on a finer dyadic level `m ≥ n`. The refinement keeps the integrand
adapted and its compensated integral unchanged, so integrands of different resolutions can be
compared on a common grid.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Doob `L²` machinery (toward the càdlàg conjunct of #6)

Mathlib has only the discrete *tail* maximal inequality (`maximal_ineq`), the
layer-cake formula, and conditional Jensen. The continuous-time Doob `L²` maximal
inequality and the càdlàg regularization are built here from those pieces. -/

/-! ### Cross-resolution refinement (toward the `L²(P)` Cauchy property)

To compare the step integrals of two density approximants at *different* dyadic
levels, both are re-expressed on the common (finer) dyadic refinement. The basic
brick is additivity of the compensated integral over a split time-interval. -/

theorem _root_.LevyStochCalc.Poisson.Compensated.stepIntegral_dyadic_refine_integral
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) {T : ℝ} (hT : 0 < T) {n m : ℕ}
    (hnm : n ≤ m) {Ki : Fin (2 ^ n) → ℕ} (Bi : ∀ i, Fin (Ki i) → Set E)
    (ci : ∀ i, Fin (Ki i) → Ω → ℝ)
    (hBim : ∀ i k, MeasurableSet (Bi i k)) (hBif : ∀ i k, ν (Bi i k) ≠ ⊤) :
    (fun ω => ∑ i' : Fin (2 ^ m), ∑ k₀ : Fin (Ki (dyadicCoarse n m hnm i')),
        ci (dyadicCoarse n m hnm i') k₀ ω
        * N.compensated (Set.Ioc (dyadicPartition T m i'.castSucc) (dyadicPartition T m i'.succ)
            ×ˢ Bi (dyadicCoarse n m hnm i') k₀) ω)
      =ᵐ[P] fun ω => ∑ i : Fin (2 ^ n), ∑ k₀, ci i k₀ ω
        * N.compensated (Set.Ioc (dyadicPartition T n i.castSucc) (dyadicPartition T n i.succ)
            ×ˢ Bi i k₀) ω := by sorry
