-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_markStepIntegral_diff_isometry
-- name    : LevyStochCalc.Poisson.Compensated.markStepIntegral_diff_isometry
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T09:54:39.258179+00:00
-- url     : https://prove2.me/theorems/c5e05e7f-df57-4f70-902c-c22a701a72a6
-- title:
--   markStepIntegral diff isometry
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.markStepIntegral_diff_isometry` is extracted from `LevyStochCalc.Poisson.CompensatedDensityRefinement`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRefinement_F001

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

theorem _root_.LevyStochCalc.Poisson.Compensated.markStepIntegral_diff_isometry
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ) {N₀ : ℕ} (p : Fin (N₀ +
      1) → ℝ)
    (hp0 : p 0 = 0) (hpmono : StrictMono p) {T : ℝ} (hpleT : p (Fin.last N₀) ≤ T)
    {Ki1 Ki2 : Fin N₀ → ℕ} (Bi1 : ∀ i, Fin (Ki1 i) → Set E) (Bi2 : ∀ i, Fin (Ki2 i) → Set E)
    (ci1 : ∀ i, Fin (Ki1 i) → Ω → ℝ) (ci2 : ∀ i, Fin (Ki2 i) → Ω → ℝ)
    (hBi1m : ∀ i k, MeasurableSet (Bi1 i k)) (hBi2m : ∀ i k, MeasurableSet (Bi2 i k))
    (hBi1f : ∀ i k, ν (Bi1 i k) ≠ ⊤) (hBi2f : ∀ i k, ν (Bi2 i k) ≠ ⊤)
    (hci1b : ∀ i k, ∃ M, ∀ ω, |ci1 i k ω| ≤ M) (hci2b : ∀ i k, ∃ M, ∀ ω, |ci2 i k ω| ≤ M)
    (hci1m : ∀ i k, Measurable (ci1 i k)) (hci2m : ∀ i k, Measurable (ci2 i k))
    (hci1a : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (p i.castSucc)) (ci1 i k))
    (hci2a : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (p i.castSucc)) (ci2 i k)) :
    ∫ ω, ((∑ i : Fin N₀, ∑ k₀, ci1 i k₀ ω
          * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ Bi1 i k₀) ω)
        - ∑ i : Fin N₀, ∑ k₀, ci2 i k₀ ω
          * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ Bi2 i k₀) ω) ^ 2 ∂P
      = ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) T,
        ((∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
            * ∑ k₀, ci1 i k₀ ω * (Bi1 i k₀).indicator (fun _ => (1 : ℝ)) e)
          - ∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
            * ∑ k₀, ci2 i k₀ ω * (Bi2 i k₀).indicator (fun _ => (1 : ℝ)) e) ^ 2
        ∂volume ∂ν) ∂P := by sorry
