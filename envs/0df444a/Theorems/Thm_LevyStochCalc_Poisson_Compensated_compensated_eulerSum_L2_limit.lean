-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_compensated_eulerSum_L2_limit
-- name    : LevyStochCalc.Poisson.Compensated.compensated_eulerSum_L2_limit
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T09:58:46.097784+00:00
-- url     : https://prove2.me/theorems/e41b6074-6759-4c35-84b0-9f0d2c72edb6
-- title:
--   compensated eulerSum L2 limit
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.compensated_eulerSum_L2_limit` is extracted from `LevyStochCalc.Poisson.CompensatedDensityLimit`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityLimit_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The cross-resolution Cauchy estimate and the `L²` limit

The isometry for the difference of two step integrals at different dyadic resolutions, the
resulting Cauchy estimate for the Euler sums of a bounded predictable integrand, and the limit
in `L²(P)` it produces. Closing bricks on the regularity of monotone `ℝ≥0∞`-valued functions of
time and the right-continuity of the intensity of shrinking time-mark boxes support the path
regularity of that limit.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

theorem _root_.LevyStochCalc.Poisson.Compensated.compensated_eulerSum_L2_limit
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T) (φ
      : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M)
    {S : Set E} (hS : MeasurableSet S) (hSfin : ν S ≠ ⊤)
    (hSupp : ∀ ω e, e ∉ S → ∀ u, φ ω u e = 0) :
    ∃ (Ki : (n : ℕ) → Fin (2 ^ n) → ℕ)
      (Bi : (n : ℕ) → (i : Fin (2 ^ n)) → Fin (Ki n i) → Set E)
      (ci : (n : ℕ) → (i : Fin (2 ^ n)) → Fin (Ki n i) → Ω → ℝ) (F : Ω → ℝ),
      MeasureTheory.MemLp F 2 P ∧
      Filter.Tendsto (fun n => MeasureTheory.eLpNorm
        ((fun ω => ∑ i : Fin (2 ^ n), ∑ k, ci n i k ω
          * N.compensated (Set.Ioc (dyadicPartition T n i.castSucc)
              (dyadicPartition T n i.succ) ×ˢ Bi n i k) ω) - F) 2 P) Filter.atTop (nhds 0) := by sorry
