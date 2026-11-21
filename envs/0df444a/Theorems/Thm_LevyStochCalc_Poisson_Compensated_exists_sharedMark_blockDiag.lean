-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_exists_sharedMark_blockDiag
-- name    : LevyStochCalc.Poisson.Compensated.exists_sharedMark_blockDiag
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T09:21:49.324185+00:00
-- url     : https://prove2.me/theorems/4ebf6f90-c789-413e-bd4c-88e1cefa5e31
-- title:
--   exists sharedMark blockDiag
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.exists_sharedMark_blockDiag` is extracted from `LevyStochCalc.Poisson.CompensatedDensityRefinement`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRefinement_F000

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

theorem _root_.LevyStochCalc.Poisson.Compensated.exists_sharedMark_blockDiag
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (_N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {N₀ : ℕ} (p : Fin (N₀ + 1) → ℝ)
    {Ki : Fin N₀ → ℕ} (Bi : ∀ i, Fin (Ki i) → Set E) (ci : ∀ i, Fin (Ki i) → Ω → ℝ)
    (hBim : ∀ i k, MeasurableSet (Bi i k)) (hBif : ∀ i k, ν (Bi i k) ≠ ⊤)
    (hcib : ∀ i k, ∃ M, ∀ ω, |ci i k ω| ≤ M) (hcim : ∀ i k, Measurable (ci i k))
    (hcia : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (p i.castSucc)) (ci i k)) :
    ∃ (K : ℕ) (B : Fin K → Set E) (ξ : Fin N₀ → Fin K → Ω → ℝ),
      (∀ k, MeasurableSet (B k)) ∧ (∀ k, ν (B k) ≠ ⊤) ∧
      (∀ i k, ∃ M, ∀ ω, |ξ i k ω| ≤ M) ∧ (∀ i k, Measurable (ξ i k)) ∧
      (∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (p i.castSucc)) (ξ i k)) ∧
      (∀ (i : Fin N₀) (ω : Ω) (F : Set E → ℝ),
        (∑ k, ξ i k ω * F (B k)) = ∑ k₀, ci i k₀ ω * F (Bi i k₀)) := by sorry
