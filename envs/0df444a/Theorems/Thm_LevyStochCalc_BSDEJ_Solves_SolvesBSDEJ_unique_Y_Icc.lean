-- Prove2me | Theorems.Thm_LevyStochCalc_BSDEJ_Solves_SolvesBSDEJ_unique_Y_Icc
-- name    : LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ.unique_Y_Icc
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T08:15:21.400984+00:00
-- url     : https://prove2.me/theorems/51dd6738-d955-48f8-aa64-4ff08a4709c6
-- title:
--   unique Y Icc
-- statement:
--   The source theorem `LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ.unique_Y_Icc` is extracted from `LevyStochCalc.BSDEJ.Uniqueness`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_Uniqueness_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Uniqueness of solutions of a backward equation with jumps

A solution of a backward equation with jumps over the augmented joint filtration of a Lévy
driver is its own Picard output, so the difference of two solutions with the same generator,
terminal value and horizon is a fixed point of the Picard contraction: its exponentially
weighted norm at the Young weight `max 2 (24 L²)` is at most a quarter of itself and finite,
hence zero. The value processes then agree almost surely at almost every time of the horizon,
and, both being right-continuous, at every time of the horizon; the diffusion coordinates and
the jump integrand agree up to sets of zero energy.

## Main statements

* `LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ.toPicardOutput` — a solution is its own Picard output.
* `LevyStochCalc.BSDEJ.Solves.exists_drift_of_solvesBSDEJ` — the generator evaluated along a
  solution has a jointly and progressively measurable version of finite energy.
* `LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ.unique` — the weighted norm of the difference of two
  solutions vanishes.
* `LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ.unique_Y_ae`,
  `LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ.unique_Y_Icc`,
  `LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ.unique_Z`,
  `LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ.unique_U` — the three components of two solutions
  agree.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Auxiliary facts -/

/-! ### A solution is its own Picard output -/

/-! ### The drift along a solution -/

/-! ### Uniqueness -/

/-! ### Consequences -/

theorem _root_.LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ.unique_Y_Icc {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ} {ξ : Ω → ℝ} {T : ℝ}
    {Y₁ Y₂ : ℝ → Ω → ℝ} {Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ)} {U₁ U₂ : ℝ → Ω → E → ℝ}
    (h₁ : SolvesBSDEJ D f ξ T Y₁ Z₁ U₁) (h₂ : SolvesBSDEJ D f ξ T Y₂ Z₂ U₂) (hT : 0 < T)
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u)
    (hL : 0 ≤ L)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ t =ᵐ[P] Y₂ t := by sorry
