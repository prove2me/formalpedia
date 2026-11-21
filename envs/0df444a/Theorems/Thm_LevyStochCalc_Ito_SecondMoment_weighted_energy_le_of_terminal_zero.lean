-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_SecondMoment_weighted_energy_le_of_terminal_zero
-- name    : LevyStochCalc.Ito.SecondMoment.weighted_energy_le_of_terminal_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T22:39:52.721596+00:00
-- url     : https://prove2.me/theorems/05ba30d4-504e-4ff2-8244-a10ccd93aea6
-- title:
--   weighted energy le of terminal zero
-- statement:
--   The source theorem `LevyStochCalc.Ito.SecondMoment.weighted_energy_le_of_terminal_zero` is extracted from `LevyStochCalc.Ito.SecondMomentBackward`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_SecondMomentBackward_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The backward weighted energy inequality

For an Itô–Lévy process `X` over a Lévy driver that vanishes at a horizon `T`, the exponentially
weighted second moment identity

`e^{βT} 𝔼[X_T²] = 𝔼[X₀²] + ∫_0^T e^{βs} (β 𝔼[X_s²] + 2 𝔼[X_s b_s] + ∑_j 𝔼[σ_j(s)²]
  + 𝔼 ∫_E γ(s, e)² ν(de)) ds`

has vanishing left-hand side and a nonnegative initial term, so the weighted energy of the
process and of its two integrands is dominated by the weighted pairing of the process against
the negated drift,

`∫_0^T e^{βs} (β 𝔼[X_s²] + ∑_j 𝔼[σ_j(s)²] + 𝔼 ∫_E γ(s, e)² ν(de)) ds
  ≤ ∫_0^T e^{βs} · 2 𝔼[X_s (-b_s)] ds`,

the backward form in which the a-priori estimates for BSDEs with jumps read the quadratic Itô
formula.

## Main statements

* `weighted_energy_le_of_terminal_zero` — the inequality, with the drift negated inside the
  pairing on the right.
* `weighted_energy_le_of_terminal_zero'` — the same with the drift left as it stands and the
  sign carried outside the time integral.
* `integrableOn_integral_mul_self` — the second moment of an Itô–Lévy process is integrable in
  time on every window.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Prelim

end Prelim

section Backward

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}

theorem _root_.LevyStochCalc.Ito.SecondMoment.weighted_energy_le_of_terminal_zero
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N
      (LevyStochCalc.Brownian.augFiltration D.filtration P) D.isBrownianFiltration_aug
      D.isPoissonFiltration_aug X X₀ b σ γ)
    (hX₀ : StronglyMeasurable[LevyStochCalc.Brownian.augFiltration D.filtration P 0] X₀)
    (hX₀2 : MemLp X₀ 2 P)
    (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbp : LevyStochCalc.Probability.ProgressivelyMeasurable
      (LevyStochCalc.Brownian.augFiltration D.filtration P) fun ω s => b s ω)
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (β : ℝ) {T : ℝ} (hT : 0 < T) (hXT : X T =ᵐ[P] 0) :
    ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s)
        * (β * ∫ ω, X s ω * X s ω ∂P
          + (∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
          + (∫⁻ ω, ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal)
      ≤ ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * (2 * ∫ ω, X s ω * (-b s ω) ∂P) := by sorry
