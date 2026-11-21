-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_timeAug
-- name    : LevyStochCalc.Brownian.Ito.IsVectorItoVersion.timeAug
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:40:15.31509+00:00
-- url     : https://prove2.me/theorems/d4fb696e-8a83-4901-9b84-5a9a346930de
-- title:
--   timeAug
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.timeAug` is extracted from `LevyStochCalc.Brownian.VectorItoTimeAug`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoTimeAug_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Time as a state coordinate

Prepending a coordinate that drifts at unit rate and carries no diffusion turns a vector Itô
process `X` on `Fin n → ℝ` into one on `Fin (n + 1) → ℝ` whose path is `t ↦ (t, X_t)`. Itô's
formula for a time-dependent function of the state is then the state-only formula for the
augmented process.

## Main statements

* `LevyStochCalc.Brownian.Ito.timeAugDiffusion`, `timeAugDrift`, `timeAugInit`,
  `timeAugProcess` — the augmented data.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.timeAug` — the augmented path is a version of
  the augmented Itô process.
* `LevyStochCalc.Brownian.Ito.measurable_timeAugWeight` and its companions — the Itô formula's
  integrand hypotheses transfer to the augmented indices.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section Data

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

variable (H : Fin n → Fin d → Ω → ℝ → ℝ)

variable (bdrift : Fin n → Ω → ℝ → ℝ)

end Data

section Version

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
  {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)}
  {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}

theorem _root_.LevyStochCalc.Brownian.Ito.IsVectorItoVersion.timeAug
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) :
    IsVectorItoVersion W ℱ hcoord (timeAugDiffusion H)
      (measurable_timeAugDiffusion H hHm) (progressivelyMeasurable_timeAugDiffusion H ℱ hHp)
      (sq_timeAugDiffusion H hHs) (timeAugInit X₀) (timeAugDrift bdrift)
      (timeAugProcess X) := by sorry
