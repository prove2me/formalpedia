-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_progressive_energy_limit
-- name    : LevyStochCalc.Brownian.Ito.exists_progressive_energy_limit
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T22:17:16.48394+00:00
-- url     : https://prove2.me/theorems/dda986b4-b68a-428b-9950-698c29947f38
-- title:
--   exists progressive energy limit
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.exists_progressive_energy_limit` is extracted from `LevyStochCalc.Brownian.ItoIntegrandComplete`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIntegrandComplete_F001
import Definitions.Def_LevyStochCalc_Probability_Progressive_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Completeness of the admissible integrands on a horizon

The energy of an integrand over `[0, T]` is the square of its `L²`-seminorm for the product of
the sample measure with Lebesgue measure on the horizon. A sequence of integrands that is Cauchy
for that energy therefore has an `L²`-limit, and the pointwise `limsup` of an almost everywhere
convergent subsequence is a representative of that limit which is again progressively measurable.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Complete

variable {T : ℝ} {H : ℕ → Ω → ℝ → ℝ}

omit [IsProbabilityMeasure P] in

theorem _root_.LevyStochCalc.Brownian.Ito.exists_progressive_energy_limit (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hm : ∀ n, Measurable (Function.uncurry (H n)))
    (hp : ∀ n, Probability.ProgressivelyMeasurable ℱ (H n))
    (hz : ∀ n ω s, s ∉ Set.Icc (0 : ℝ) T → H n ω s = 0)
    (hfin : ∀ n, energy P T (H n) ≠ ⊤)
    (hcau : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      energy P T (fun ω s => H m ω s - H n ω s) < ε) :
    ∃ K : Ω → ℝ → ℝ, Measurable (Function.uncurry K)
      ∧ Probability.ProgressivelyMeasurable ℱ K
      ∧ (∀ ω s, s ∉ Set.Icc (0 : ℝ) T → K ω s = 0)
      ∧ energy P T K ≠ ⊤
      ∧ Tendsto (fun n => energy P T (fun ω s => H n ω s - K ω s)) atTop (𝓝 0) := by sorry
