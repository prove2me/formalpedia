-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_IntegralLimit_exists_seq_ae_tendsto_compensatedStochasticIntegral_of_dominated
-- name    : LevyStochCalc.Ito.IntegralLimit.exists_seq_ae_tendsto_compensatedStochasticIntegral_of_dominated
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T08:03:35.900579+00:00
-- url     : https://prove2.me/theorems/c47af658-e82b-4c29-9c45-c0dc84ab9f64
-- title:
--   exists seq ae tendsto compensatedStochasticIntegral of dominated
-- statement:
--   The source theorem `LevyStochCalc.Ito.IntegralLimit.exists_seq_ae_tendsto_compensatedStochasticIntegral_of_dominated` is extracted from `LevyStochCalc.Ito.StochasticIntegralLimit`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Limits of stochastic integrals along dominated sequences of integrands

A sequence of integrands converging pointwise almost everywhere and dominated by a
square-integrable function converges to its limit in the energy norm, over `P ⊗ ds` for a
Brownian integrand and over `P ⊗ ds ⊗ ν` for a marked one. Through the `L²` isometries of the
Itô and compensated Itô–Lévy integrals this transfers to the integrals themselves: they converge
in `L²`, hence almost surely along a subsequence.

## Main statements

All statements live in the `LevyStochCalc.Ito.IntegralLimit` namespace.

* `tendsto_lintegral_sq_sub_of_dominated` — dominated convergence in the energy norm over
  `P ⊗ ds`.
* `tendsto_lintegral_sq_sub_mark_of_dominated` — dominated convergence in the energy norm over
  `P ⊗ ds ⊗ ν`.
* `tendsto_lintegral_sq_stochasticIntegralBrownian_of_dominated` and
  `exists_seq_ae_tendsto_stochasticIntegralBrownian_of_dominated` — the Itô integrals of a
  dominated sequence of integrands converge in `L²`, and almost surely along a strictly monotone
  subsequence.
* `tendsto_lintegral_sq_compensatedStochasticIntegral_of_dominated` and
  `exists_seq_ae_tendsto_compensatedStochasticIntegral_of_dominated` — the same for the
  compensated Itô–Lévy integral.
* `tendsto_lintegral_sq_stochasticIntegral_markCut_compl` and
  `exists_seq_ae_tendsto_stochasticIntegral_markCut_compl` — the compensated Itô–Lévy integrals
  of an integrand cut to the complements of a family of mark sets that eventually misses almost
  every mark converge to the compensated Itô–Lévy integral of the integrand; the suffix
  `_of_antitone` names the same conclusions under an antitone family with null intersection.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §4.4 (Thm 4.4.7).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.IntegralLimit

universe u v

section Basic

variable {α : Type*} [MeasurableSpace α]

end Basic

section Unmarked

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

end Unmarked

section Marked

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} [SigmaFinite ν]

end Marked

section Subsequence

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

end Subsequence

section Brownian

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : Brownian.IsBrownianFiltration W ℱ)
  (H : ℕ → Ω → ℝ → ℝ) (H₀ : Ω → ℝ → ℝ) (g : Ω → ℝ → ℝ)
  (hHm : ∀ m, Measurable (Function.uncurry (H m)))
  (hHp : ∀ m, Probability.ProgressivelyMeasurable ℱ (H m))
  (hHq : ∀ (m : ℕ) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
    (‖H m ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hH₀m : Measurable (Function.uncurry H₀))
  (hH₀p : Probability.ProgressivelyMeasurable ℱ H₀)
  (hH₀q : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
    (‖H₀ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end Brownian

section Compensated

open LevyStochCalc.Poisson.Compensated

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : Poisson.IsPoissonFiltration N ℱ)
  (φ : ℕ → Ω → ℝ → E → ℝ) (φ₀ : Ω → ℝ → E → ℝ) (g : Ω → ℝ → E → ℝ)
  (hφm : ∀ m, Measurable fun p : Ω × ℝ × E => φ m p.1 p.2.1 p.2.2)
  (hφp : ∀ m, Probability.MarkedProgressivelyMeasurable ℱ (φ m))
  (hφq : ∀ (m : ℕ) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
    (‖φ m ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  (hφ₀m : Measurable fun p : Ω × ℝ × E => φ₀ p.1 p.2.1 p.2.2)
  (hφ₀p : Probability.MarkedProgressivelyMeasurable ℱ φ₀)
  (hφ₀q : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
    (‖φ₀ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hℱ in

theorem _root_.LevyStochCalc.Ito.IntegralLimit.exists_seq_ae_tendsto_compensatedStochasticIntegral_of_dominated
    (hgm : Measurable fun p : Ω × ℝ × E => g p.1 p.2.1 p.2.2) {T : ℝ} (hT : 0 < T)
    (hpt : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ e ∂ν,
      Tendsto (fun m => φ m ω s e) atTop (𝓝 (φ₀ ω s e)))
    (hdom : ∀ m, ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ e ∂ν,
      ‖φ m ω s e‖ ≤ g ω s e)
    (hg : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖g ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ (∀ i : ℕ, i ≤ k i) ∧ ∀ᵐ ω ∂P, Tendsto
      (fun m => stochasticIntegral N ℱ hℱ (φ (k m)) (hφm (k m)) (hφp (k m)) (hφq (k m)) T ω)
      atTop (𝓝 (stochasticIntegral N ℱ hℱ φ₀ hφ₀m hφ₀p hφ₀q T ω)) := by sorry
