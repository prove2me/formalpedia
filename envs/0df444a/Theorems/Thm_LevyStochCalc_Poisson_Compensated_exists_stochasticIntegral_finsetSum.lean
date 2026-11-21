-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_exists_stochasticIntegral_finsetSum
-- name    : LevyStochCalc.Poisson.Compensated.exists_stochasticIntegral_finsetSum
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:51:37.129499+00:00
-- url     : https://prove2.me/theorems/cf4bcc69-1f03-4130-87d1-00724b0791c9
-- title:
--   exists stochasticIntegral finsetSum
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.exists_stochasticIntegral_finsetSum` is extracted from `LevyStochCalc.Ito.CompensatedLocalityWindow`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityCutoff_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated integral over a time window

Restricting a marked integrand to a window `(c, t]` preserves admissibility and yields the
increment of the compensated integral across that window; an integrand vanishing after a
positive time `c` has an integral that no longer moves after `c`, the hit indicator of a
stopping time at `c` factors out of the integral over `(c, t]`, and the integral is additive in
the integrand, over differences and over finite sums.

## Main statements

* `stochasticIntegral_ae_eq_of_vanishing_gt` — the integral of an integrand vanishing after a
  time `c` does not move after `c`.
* `stochasticIntegral_indicator_Ioc` — restricting the integrand to `(c, t]` gives the increment
  of the integral over `(c, t]`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

open LevyStochCalc.Brownian.Ito (indIoc indIoc_le_one measurable_uncurry_indIoc hitInd
  abs_hitInd_le_one stronglyMeasurable_hitInd sq_nnnorm_add_le_two_mul)

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Window

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)
  {φ : Ω → ℝ → E → ℝ}
  (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (hp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ)
  (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

end Window

section Linear

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

include hℱ in

theorem _root_.LevyStochCalc.Poisson.Compensated.exists_stochasticIntegral_finsetSum {ι : Type*}
    (H : ι → Ω → ℝ → E → ℝ)
    (hmH : ∀ i, Measurable fun p : Ω × ℝ × E => H i p.1 p.2.1 p.2.2)
    (hpH : ∀ i, LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ (H i))
    (hqH : ∀ (i : ι) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖H i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (J : Finset ι) {T : ℝ} (hT : 0 < T) :
    ∃ (hms : Measurable fun p : Ω × ℝ × E => ∑ i ∈ J, H i p.1 p.2.1 p.2.2)
      (hps : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ
        fun ω s e => ∑ i ∈ J, H i ω s e)
      (hqs : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖∑ i ∈ J, H i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤),
      stochasticIntegral N ℱ hℱ (fun ω s e => ∑ i ∈ J, H i ω s e) hms hps hqs T
        =ᵐ[P] fun ω => ∑ i ∈ J,
          stochasticIntegral N ℱ hℱ (H i) (hmH i) (hpH i) (hqH i) T ω := by sorry
