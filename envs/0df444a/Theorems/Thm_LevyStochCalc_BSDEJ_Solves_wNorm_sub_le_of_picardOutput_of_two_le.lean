-- Prove2me | Theorems.Thm_LevyStochCalc_BSDEJ_Solves_wNorm_sub_le_of_picardOutput_of_two_le
-- name    : LevyStochCalc.BSDEJ.Solves.wNorm_sub_le_of_picardOutput_of_two_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T23:32:27.452859+00:00
-- url     : https://prove2.me/theorems/a1ac539a-c455-490b-89a4-15bc62305dde
-- title:
--   wNorm sub le of picardOutput of two le
-- statement:
--   The source theorem `LevyStochCalc.BSDEJ.Solves.wNorm_sub_le_of_picardOutput_of_two_le` is extracted from `LevyStochCalc.BSDEJ.PicardContractionContraction`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionBounds_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Picard contraction

One Picard step contracts the exponentially weighted `L²` norm of a triple: the weighted norm of
the difference of two Picard outputs is at most `6 L² / β` times the weighted norm of the
difference of their input triples at every Young weight `β ≥ 2`, and hence at most `1 / 4` times
it at the Young weight `β = max 2 (24 L²)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

section Contraction

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

theorem _root_.LevyStochCalc.BSDEJ.Solves.wNorm_sub_le_of_picardOutput_of_two_le
    {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    {T : ℝ} (hT : 0 < T) {ξ : Ω → ℝ}
    {Y'₁ Y₁ Y'₂ Y₂ : ℝ → Ω → ℝ} {Z'₁ Z₁ Z'₂ Z₂ : ℝ → Ω → (Fin d → ℝ)}
    {U'₁ U₁ U'₂ U₂ : ℝ → Ω → E → ℝ}
    (h₁ : PicardOutput D f ξ T Y'₁ Z'₁ U'₁ Y₁ Z₁ U₁)
    (h₂ : PicardOutput D f ξ T Y'₂ Z'₂ U'₂ Y₂ Z₂ U₂)
    (hY'm : Measurable (Function.uncurry fun ω s => Y'₁ s ω - Y'₂ s ω))
    (hZ'm : ∀ j, Measurable (Function.uncurry fun ω s => Z'₁ s ω j - Z'₂ s ω j))
    (hU'm : Measurable fun p : Ω × ℝ × E => U'₁ p.2.1 p.1 p.2.2 - U'₂ p.2.1 p.1 p.2.2)
    {b₁ b₂ : Ω → ℝ → ℝ} (hb₁m : Measurable (Function.uncurry b₁))
    (hb₁p : Probability.ProgressivelyMeasurable (augJoint D) b₁)
    (hb₁z : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b₁ ω s = 0)
    (hb₁q : Brownian.Ito.energy P T b₁ ≠ ⊤)
    (hb₁ : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      b₁ p.1 p.2 = f p.2 (Y'₁ p.2 p.1) (Z'₁ p.2 p.1) (U'₁ p.2 p.1))
    (hb₂m : Measurable (Function.uncurry b₂))
    (hb₂p : Probability.ProgressivelyMeasurable (augJoint D) b₂)
    (hb₂z : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b₂ ω s = 0)
    (hb₂q : Brownian.Ito.energy P T b₂ ≠ ⊤)
    (hb₂ : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      b₂ p.1 p.2 = f p.2 (Y'₂ p.2 p.1) (Z'₂ p.2 p.1) (U'₂ p.2 p.1))
    {β : ℝ} (hβ : 2 ≤ β)
    (hin : wNorm P ν β T (fun t ω => Y'₁ t ω - Y'₂ t ω) (fun t ω => Z'₁ t ω - Z'₂ t ω)
      (fun t ω e => U'₁ t ω e - U'₂ t ω e) ≠ ⊤) :
    wNorm P ν β T (fun t ω => Y₁ t ω - Y₂ t ω) (fun t ω => Z₁ t ω - Z₂ t ω)
        (fun t ω e => U₁ t ω e - U₂ t ω e)
      ≤ ENNReal.ofReal (6 * L ^ 2 / β) * wNorm P ν β T (fun t ω => Y'₁ t ω - Y'₂ t ω)
        (fun t ω => Z'₁ t ω - Z'₂ t ω) (fun t ω e => U'₁ t ω e - U'₂ t ω e) := by sorry
