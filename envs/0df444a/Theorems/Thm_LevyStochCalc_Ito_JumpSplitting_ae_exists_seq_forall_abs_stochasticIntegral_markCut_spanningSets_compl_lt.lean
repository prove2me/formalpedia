-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpSplitting_ae_exists_seq_forall_abs_stochasticIntegral_markCut_spanningSets_compl_lt
-- name    : LevyStochCalc.Ito.JumpSplitting.ae_exists_seq_forall_abs_stochasticIntegral_markCut_spanningSets_compl_lt
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T08:19:12.761601+00:00
-- url     : https://prove2.me/theorems/b36ba81e-9243-4319-8a21-6d21ded7ea38
-- title:
--   ae exists seq forall abs stochasticIntegral markCut spanningSets compl lt
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpSplitting.ae_exists_seq_forall_abs_stochasticIntegral_markCut_spanningSets_compl_lt` is extracted from `LevyStochCalc.Ito.JumpSplittingRemainderVanishing`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Theorems.Thm_LevyStochCalc_Probability_MarkedProgressivelyMeasurable_indicator_mark
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingRemainderVanishing_F000
import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Vanishing remainders and the jump of a solution

Along a subsequence of the spanning sets of the intensity the compensated integrals of a finite
family of integrands cut to the complements of those sets vanish uniformly on every bounded
window, by Doob's `L²` maximal inequality against the Itô–Lévy isometry; passing to such a
subsequence in the splitting with remainder, the jump of a jump diffusion across an arrival time
carrying a mark of a spanning set is exactly the jump coefficient read at the left limit there.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.ae_exists_atomEnum_jump_eq_gamma_of_sdeData` — the jump of a
  solution across an arrival time.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, Theorem 4.4.7, step (II).
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpSplitting

open LevyStochCalc.Poisson.Compensated

universe u v

section Uniform

open LevyStochCalc.Probability

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

omit h_meas h_progMeas h_sq in

theorem _root_.LevyStochCalc.Ito.JumpSplitting.ae_exists_seq_forall_abs_stochasticIntegral_markCut_spanningSets_compl_lt
    {ι : Type*} [Finite ι] (φ : ι → Ω → ℝ → E → ℝ)
    (hm : ∀ i, Measurable fun p : Ω × ℝ × E => φ i p.1 p.2.1 p.2.2)
    (hp : ∀ i, Probability.MarkedProgressivelyMeasurable ℱ (φ i))
    (hq : ∀ i, ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∃ ks : ℕ → ℕ, (∀ m, m ≤ ks m) ∧ ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ → ∀ᶠ m in atTop,
      ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
        |stochasticIntegral N ℱ hℱ (markCut (spanningSets ν (ks m))ᶜ (φ i))
          (measurable_markCut (hm i) (measurableSet_spanningSets ν (ks m)).compl)
          ((hp i).indicator_mark (measurableSet_spanningSets ν (ks m)).compl)
          (fun T' hT' => sq_markCut (hq i) (spanningSets ν (ks m))ᶜ T' hT') t ω| < δ := by sorry
