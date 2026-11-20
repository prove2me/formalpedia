-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_exists_markEval_L2_tendsto
-- name    : LevyStochCalc.Poisson.Compensated.exists_markEval_L2_tendsto
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T22:47:25.502+00:00
-- url     : https://prove2.me/theorems/c242ec1f-2c5d-40a7-ade7-b9ffd57836ea
-- title:
--   exists markEval L2 tendsto
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.exists_markEval_L2_tendsto` is extracted from `LevyStochCalc.Poisson.CompensatedDensityMarkApprox`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkApprox_F001
import Definitions.Def_LevyStochCalc_Poisson_RandomMeasure_F000

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

theorem _root_.LevyStochCalc.Poisson.Compensated.exists_markEval_L2_tendsto
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {T : ℝ} (hT : 0 < T)
    (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M)
    {S : Set E} (hS : MeasurableSet S) (hSfin : ν S ≠ ⊤)
    (hSupp : ∀ ω e, e ∉ S → ∀ u, φ ω u e = 0) :
    ∃ (Ki : (n : ℕ) → Fin (2 ^ n) → ℕ)
      (Bi : (n : ℕ) → (i : Fin (2 ^ n)) → Fin (Ki n i) → Set E)
      (ci : (n : ℕ) → (i : Fin (2 ^ n)) → Fin (Ki n i) → Ω → ℝ),
      (∀ n i k, MeasurableSet (Bi n i k)) ∧ (∀ n i k, Bi n i k ⊆ S) ∧
      (∀ n i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (dyadicPartition T n i.castSucc))
        (ci n i k)) ∧
      (∀ n i k, ∃ C, ∀ ω, |ci n i k ω| ≤ C) ∧
      Filter.Tendsto (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e - ∑ i : Fin (2 ^ n),
            (Set.Ioc (dyadicPartition T n i.castSucc) (dyadicPartition T n i.succ)).indicator
              (fun _ => (1 : ℝ)) s
            * ∑ k, ci n i k ω * (Bi n i k).indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2
        ∂ν ∂volume ∂P) Filter.atTop (nhds 0) := by sorry
