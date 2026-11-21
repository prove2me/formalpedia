-- Prove2me | Theorems.Thm_LevyStochCalc_BSDEJ_Solves_ae_two_mul_integral_mul_sub_le
-- name    : LevyStochCalc.BSDEJ.Solves.ae_two_mul_integral_mul_sub_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T23:33:17.925952+00:00
-- url     : https://prove2.me/theorems/c27513a8-1fde-491f-a237-d0f46c93390e
-- title:
--   ae two mul integral mul sub le
-- statement:
--   The source theorem `LevyStochCalc.BSDEJ.Solves.ae_two_mul_integral_mul_sub_le` is extracted from `LevyStochCalc.BSDEJ.PicardContractionBounds`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionBounds_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Energy and pointwise bounds behind the Picard contraction

The energy of a process on a horizon is at most the length of the horizon times its `S²`
seminorm, the energy of a difference of two processes is finite when both energies are, and
freezing a process at the horizon leaves its energy there unchanged. At almost every time of the
horizon, twice the pairing of a process against the difference of two evaluations of a Lipschitz
generator is at most `β / 2` times the second moment of the process plus `6 L² / β` times the
sample energy density of the differenced arguments, and the real-variable core turns a weighted
energy dominated by such a pairing into a contraction by the factor `6 L² / β`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

section Energies

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {T : ℝ}

end Energies

section Pointwise

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {β T : ℝ}

theorem _root_.LevyStochCalc.BSDEJ.Solves.ae_two_mul_integral_mul_sub_le
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (hβ : 0 < β) {X : ℝ → Ω → ℝ} {b₁ b₂ : Ω → ℝ → ℝ}
    {Y'₁ Y'₂ : ℝ → Ω → ℝ} {Z'₁ Z'₂ : ℝ → Ω → (Fin d → ℝ)} {U'₁ U'₂ : ℝ → Ω → E → ℝ}
    {ΔY : ℝ → Ω → ℝ} {ΔZ : ℝ → Ω → (Fin d → ℝ)} {ΔU : ℝ → Ω → E → ℝ}
    (hΔY : ∀ s ω, ΔY s ω = Y'₁ s ω - Y'₂ s ω)
    (hΔZ : ∀ s ω j, ΔZ s ω j = Z'₁ s ω j - Z'₂ s ω j)
    (hΔU : ∀ s ω e, ΔU s ω e = U'₁ s ω e - U'₂ s ω e)
    (hXm : Measurable (Function.uncurry fun ω s => X s ω))
    (hXq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖X s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hb₁m : Measurable (Function.uncurry b₁)) (hb₂m : Measurable (Function.uncurry b₂))
    (hbq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b₁ ω s - b₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hb₁ : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      b₁ p.1 p.2 = f p.2 (Y'₁ p.2 p.1) (Z'₁ p.2 p.1) (U'₁ p.2 p.1))
    (hb₂ : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      b₂ p.1 p.2 = f p.2 (Y'₂ p.2 p.1) (Z'₂ p.2 p.1) (U'₂ p.2 p.1))
    (hΔYm : Measurable (Function.uncurry fun ω s => ΔY s ω))
    (hΔZm : ∀ j, Measurable (Function.uncurry fun ω s => ΔZ s ω j))
    (hΔUm : Measurable fun p : Ω × ℝ × E => ΔU p.2.1 p.1 p.2.2)
    (hin : wNorm P ν β T ΔY ΔZ ΔU ≠ ⊤) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      2 * ∫ ω, X s ω * (b₁ ω s - b₂ ω s) ∂P
        ≤ β / 2 * (∫ ω, X s ω * X s ω ∂P)
          + 6 * L ^ 2 / β * (∫⁻ ω, density ν ΔY ΔZ ΔU ω s ∂P).toReal := by sorry
