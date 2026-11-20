-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_exists_marked_progressive_energy_limit
-- name    : LevyStochCalc.Poisson.Compensated.exists_marked_progressive_energy_limit
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T22:34:07.965363+00:00
-- url     : https://prove2.me/theorems/6c920dc4-4f3b-4e37-aec6-ff436fa02c99
-- title:
--   exists marked progressive energy limit
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.exists_marked_progressive_energy_limit` is extracted from `LevyStochCalc.Poisson.CompensatedIntegrandComplete`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedIntegrandComplete_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Completeness of the marked integrands

The marked energy of an integrand over a horizon is the square of its `L²`-seminorm for the
product of the sample measure, Lebesgue measure on the horizon and the mark measure. That space is
complete, so an energy-Cauchy sequence of admissible marked integrands has a limit; a pointwise
`limsup` along an almost-everywhere convergent subsequence provides a genuinely progressively
measurable representative of it.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Complete

variable {T : ℝ} {φ : ℕ → Ω → ℝ → E → ℝ}

omit [IsProbabilityMeasure P] in

theorem _root_.LevyStochCalc.Poisson.Compensated.exists_marked_progressive_energy_limit (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hm : ∀ n, Measurable fun p : Ω × ℝ × E => φ n p.1 p.2.1 p.2.2)
    (hp : ∀ n, Probability.MarkedProgressivelyMeasurable ℱ (φ n))
    (hz : ∀ n ω s e, s ∉ Set.Icc (0 : ℝ) T → φ n ω s e = 0)
    (hfin : ∀ n, markedEnergy P ν T (φ n) ≠ ⊤)
    (hcau : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      markedEnergy P ν T (fun ω s e => φ m ω s e - φ n ω s e) < ε) :
    ∃ ψ : Ω → ℝ → E → ℝ, Measurable (fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
      ∧ Probability.MarkedProgressivelyMeasurable ℱ ψ
      ∧ (∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → ψ ω s e = 0)
      ∧ markedEnergy P ν T ψ ≠ ⊤
      ∧ Tendsto (fun n => markedEnergy P ν T (fun ω s e => φ n ω s e - ψ ω s e)) atTop (𝓝 0) := by sorry
