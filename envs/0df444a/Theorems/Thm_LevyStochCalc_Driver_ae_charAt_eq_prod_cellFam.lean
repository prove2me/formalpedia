-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_ae_charAt_eq_prod_cellFam
-- name    : LevyStochCalc.Driver.ae_charAt_eq_prod_cellFam
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T21:44:36.251347+00:00
-- url     : https://prove2.me/theorems/48feea0a-d6c5-471d-b1d7-698eac248626
-- title:
--   ae charAt eq prod cellFam
-- statement:
--   The source theorem `LevyStochCalc.Driver.ae_charAt_eq_prod_cellFam` is extracted from `LevyStochCalc.Driver.JointGrid`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointGrid_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The joint character of a grid of cells

Counts are additive over the cells of a grid, so the Poisson character at a grid point is the
product of the characters of the families cut by the cells. Pairing that product with the
character of the Brownian increments along the same grid gives the joint grid character, which
the induction of the joint predictable representation consumes one cell at a time.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section CellFamily

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in

theorem _root_.LevyStochCalc.Driver.ae_charAt_eq_prod_cellFam (N : PoissonRandomMeasure P ν) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) {τ : ℕ → ℝ} (hτ0 : τ 0 = 0) {n : ℕ}
    (hτ : ∀ k, k < n → τ k ≤ τ (k + 1)) :
    ∀ᵐ ω ∂P, charAt N w Bfam (τ n) ω
      = ∏ k ∈ Finset.range n, charAt N w (cellFam Bfam τ k) (τ (k + 1)) ω := by sorry
