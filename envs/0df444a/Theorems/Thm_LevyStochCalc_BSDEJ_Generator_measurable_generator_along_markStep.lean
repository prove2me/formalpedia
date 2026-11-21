-- Prove2me | Theorems.Thm_LevyStochCalc_BSDEJ_Generator_measurable_generator_along_markStep
-- name    : LevyStochCalc.BSDEJ.Generator.measurable_generator_along_markStep
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:31:17.294342+00:00
-- url     : https://prove2.me/theorems/69ac2baa-6d3c-4060-b26d-05bd70987e0f
-- title:
--   measurable generator along markStep
-- statement:
--   The source theorem `LevyStochCalc.BSDEJ.Generator.measurable_generator_along_markStep` is extracted from `LevyStochCalc.BSDEJ.GeneratorAlongMarkStep`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_GeneratorAlongMarkStep_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The generator of a BSDEJ along a mark-step jump integrand

A generator `f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ` that is measurable in `(s, y, z)` for each
fixed jump variable and Lipschitz in `(y, z, u)` for the `L²(ν)` distance on the jump variable
depends on a finite combination `∑ₖ cₖ 1_{Bₖ}` of mark sets of finite measure only through the
coefficient vector `c`, continuously, so `(p, c) ↦ f p.1 p.2.1 p.2.2 (∑ₖ cₖ 1_{Bₖ})` is jointly
measurable.

A mark-step integrand `G` is such a combination at every `(ω, s)`, with coefficient vector
`markStepCoeff G ω s`; consequently the composite process
`(ω, s) ↦ f s (Y s ω) (Z s ω) (fun e => G.eval s e ω)` is jointly measurable, and progressively
measurable for a filtration to which `Y`, `Z` and the coefficients of `G` are adapted.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Generator

open LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {ν : Measure E} {d : ℕ}

/-! ### Finite combinations of mark sets -/

/-! ### The generator along a mark-step integrand -/

section MarkStep

variable [SigmaFinite ν] {g : TimeGrid}

theorem _root_.LevyStochCalc.BSDEJ.Generator.measurable_generator_along_markStep {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ}
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u) {L : ℝ}
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (G : MarkStep Ω E ν g) {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    (hYm : Measurable (Function.uncurry Y))
    (hZm : ∀ i, Measurable (Function.uncurry fun ω s => Z s ω i)) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      f s (Y s ω) (Z s ω) (fun e => G.eval s e ω)) := by sorry
