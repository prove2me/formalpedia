-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_exists_markEval_close_dyadic
-- name    : LevyStochCalc.Poisson.Compensated.exists_markEval_close_dyadic
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T22:45:01.73819+00:00
-- url     : https://prove2.me/theorems/1df5c1f8-2aff-45f2-a013-e81ad4dd81c6
-- title:
--   exists markEval close dyadic
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.exists_markEval_close_dyadic` is extracted from `LevyStochCalc.Poisson.CompensatedDensityMarkApprox`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkApprox_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Mark discretisation of the shifted dyadic eval

Approximation of the mark dependence of the adapted dyadic eval by finite mark-simple functions
`∑ₖ cₖ(ω) 𝟙_{Bₖ}(e)` with bounded, adapted coefficients, obtained by running the rectangle
density argument on each time piece over the trimmed product measure. Summing the per-piece
errors gives an `L²(P ⊗ ds ⊗ ν)` approximating sequence of adapted, mark-simple,
piecewise-constant-in-time integrands.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

theorem _root_.LevyStochCalc.Poisson.Compensated.exists_markEval_close_dyadic
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {T : ℝ} (hT : 0 < T)
    (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M)
    {S : Set E} (hS : MeasurableSet S) (hSfin : ν S ≠ ⊤)
    (hSupp : ∀ ω e, e ∉ S → ∀ u, φ ω u e = 0)
    (n : ℕ) {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ (Ki : Fin (2 ^ n) → ℕ) (Bi : ∀ i, Fin (Ki i) → Set E) (ci : ∀ i, Fin (Ki i) → Ω → ℝ),
      (∀ i k, MeasurableSet (Bi i k)) ∧ (∀ i k, Bi i k ⊆ S) ∧
      (∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (dyadicPartition T n i.castSucc))
        (ci i k)) ∧
      (∀ i k, ∃ C, ∀ ω, |ci i k ω| ≤ C) ∧
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖dyadicEvalShifted T φ n s ω e
          - ∑ i : Fin (2 ^ n),
              (Set.Ioc (dyadicPartition T n i.castSucc) (dyadicPartition T n i.succ)).indicator
                (fun _ => (1 : ℝ)) s
              * ∑ k, ci i k ω * (Bi i k).indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2
        ∂ν ∂volume ∂P ≤ ENNReal.ofReal T * δ := by sorry
