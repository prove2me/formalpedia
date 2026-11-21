-- Prove2me | Theorems.Thm_LevyStochCalc_BSDEJ_Generator_exists_progressive_generator_modification
-- name    : LevyStochCalc.BSDEJ.Generator.exists_progressive_generator_modification
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:43:44.147263+00:00
-- url     : https://prove2.me/theorems/c1ea1ea9-d42e-46c8-8bb1-731a450cb349
-- title:
--   exists progressive generator modification
-- statement:
--   The source theorem `LevyStochCalc.BSDEJ.Generator.exists_progressive_generator_modification` is extracted from `LevyStochCalc.BSDEJ.GeneratorModification`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_GeneratorModification_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A progressively measurable version of the generator along a triple of processes

A generator `f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ` that is measurable in `(s, y, z)` for each
fixed jump variable and Lipschitz in `(y, z, u)` for the `L²(ν)` distance on the jump variable is
not assumed measurable in the jump variable, so the composite `(ω, s) ↦ f s (Y s ω) (Z s ω)
(U s ω)` along a triple of processes need not be measurable. Approximating the marked process `U`
in `L²` by mark-step integrands makes the composite the pointwise limit, along a subsequence and
almost everywhere on `Ω × [0, T]`, of the jointly and progressively measurable processes obtained
by evaluating the generator along the approximants; the pointwise `limsup` of that subsequence is
then a progressively measurable process of finite energy, vanishing off the horizon, which agrees
with the composite almost everywhere.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.BSDEJ.Generator

open LevyStochCalc.Poisson.Compensated

universe u v

/-! ### Almost everywhere convergence from summable integrals -/

/-! ### The generator along a triple of processes -/

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} {d : ℕ}
  {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ}

variable [IsProbabilityMeasure P] [SigmaFinite ν] {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
  {U : ℝ → Ω → E → ℝ}

theorem _root_.LevyStochCalc.BSDEJ.Generator.exists_progressive_generator_modification (N : Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ mΩ)
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ))) {T : ℝ} (hT : 0 < T)
    (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤)
    (hYm : Measurable (Function.uncurry Y))
    (hYp : Probability.ProgressivelyMeasurable ℱ fun ω s => Y s ω)
    (hY : Brownian.Ito.energy P T (fun ω s => Y s ω) ≠ ⊤)
    (hZm : ∀ i, Measurable (Function.uncurry fun ω s => Z s ω i))
    (hZp : ∀ i, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
    (hZ : ∀ i, Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤)
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2)
    (hUp : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => U s ω e)
    (hUq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∃ b : Ω → ℝ → ℝ, Measurable (Function.uncurry b)
      ∧ Probability.ProgressivelyMeasurable ℱ b
      ∧ (∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
      ∧ Brownian.Ito.energy P T b ≠ ⊤
      ∧ ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
          b p.1 p.2 = f p.2 (Y p.2 p.1) (Z p.2 p.1) (U p.2 p.1) := by sorry
