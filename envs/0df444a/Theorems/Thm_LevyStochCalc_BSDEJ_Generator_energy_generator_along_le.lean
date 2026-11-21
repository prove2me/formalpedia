-- Prove2me | Theorems.Thm_LevyStochCalc_BSDEJ_Generator_energy_generator_along_le
-- name    : LevyStochCalc.BSDEJ.Generator.energy_generator_along_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:27:49.598118+00:00
-- url     : https://prove2.me/theorems/ebc696f3-c01b-409d-b192-76586a8452fb
-- title:
--   energy generator along le
-- statement:
--   The source theorem `LevyStochCalc.BSDEJ.Generator.energy_generator_along_le` is extracted from `LevyStochCalc.BSDEJ.GeneratorEnergy`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_GeneratorEnergy_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Energy of a BSDEJ generator along a triple of processes

A generator `f` that is Lipschitz in `(y, z, u)` for the `L²(ν)` distance of the jump variable has
linear growth: `‖f s y z u‖` is at most `‖f s 0 0 0‖ + L * (‖y‖ + ‖z‖ + ‖u‖_{L²(ν)})`, and the
square of that bound splits into four terms. Evaluated along processes `(Y, Z, U)` the splitting
dominates the energy of `s ↦ f s (Y s) (Z s) (U s)` on the horizon `[0, T]` by the energy of `Y`,
the energies of the coordinates of `Z` and the marked energy of `U`; in particular the generator
has finite energy along a triple of processes of finite energy.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Generator

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} {d : ℕ}
  {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ}

/-! ### Elementary inequalities in `ℝ≥0∞` -/

/-! ### Linear growth of a Lipschitz generator -/

/-! ### Energy along a triple of processes -/

theorem _root_.LevyStochCalc.BSDEJ.Generator.energy_generator_along_le [IsProbabilityMeasure P] [SigmaFinite ν]
    {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ} {T : ℝ}
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u)
    (hYm : Measurable (Function.uncurry Y))
    (hZm : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i))
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2) :
    Brownian.Ito.energy P T (fun ω s => f s (Y s ω) (Z s ω) (U s ω))
      ≤ 4 * ((∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2)
          + ENNReal.ofReal L ^ 2 * Brownian.Ito.energy P T (fun ω s => Y s ω)
          + ENNReal.ofReal L ^ 2 * ∑ i : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω i)
          + ENNReal.ofReal L ^ 2 *
              Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e)) := by sorry
