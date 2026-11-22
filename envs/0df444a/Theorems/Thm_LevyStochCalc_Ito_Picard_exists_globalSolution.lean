-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_exists_globalSolution
-- name    : LevyStochCalc.Ito.Picard.exists_globalSolution
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T07:45:50.135726+00:00
-- url     : https://prove2.me/theorems/8c0fe82b-bc3b-4d1b-bbf1-8e7ee6c5e0c5
-- title:
--   exists globalSolution
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.exists_globalSolution` is extracted from `LevyStochCalc.Ito.PicardGlobal`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardGlobal_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# From window solutions to a solution on `[0, ∞)`

The Bielecki contraction produces a solution on each finite window. Uniqueness on the shorter of
two windows makes the family consistent, and right-continuity upgrades that to an almost-sure
agreement of whole paths, so the windows can be glued along `⌈t⌉₊` into a single path map that
restricts to a window solution on every `[0, T]`.
-/

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-! ### Right-continuity upgrades per-time equality to path equality -/

/-! ### The glued path map -/

/-! ### Consistency of a family of window solutions -/

section Glue

variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)

theorem _root_.LevyStochCalc.Ito.Picard.exists_globalSolution [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) :
    ∃ X : ℝ → Ω → (Fin n → ℝ),
      Measurable (Function.uncurry X)
        ∧ (∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => X s ω i)
        ∧ (∀ᵐ ω ∂P, X 0 ω = x₀)
        ∧ (∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
            Filter.Tendsto (fun s => X s ω) (nhdsWithin t (Set.Ioi t)) (nhds (X t ω))
              ∧ ∀ i : Fin n, ∃ ℓ : ℝ,
                  Filter.Tendsto (fun s => X s ω i) (nhdsWithin t (Set.Iio t)) (nhds ℓ))
        ∧ (∀ T' : ℝ, 0 < T' →
            ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
        ∧ (∀ T : ℝ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T) := by sorry
