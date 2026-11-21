-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpSplitting_add_shift_eq_of_ae_forall
-- name    : LevyStochCalc.Ito.JumpSplitting.add_shift_eq_of_ae_forall
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:52:28.844051+00:00
-- url     : https://prove2.me/theorems/972cd29a-328d-4902-8ad4-c4f7293813fc
-- title:
--   add shift eq of ae forall
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpSplitting.add_shift_eq_of_ae_forall` is extracted from `LevyStochCalc.Ito.JumpSplittingAllTimes`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpSplittingAllTimes_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The finite-activity splitting at all nonnegative times

The finite-activity splitting of a jump diffusion is an identity between the path, a vector Itô
process and a pathwise jump sum, valid almost surely at each fixed nonnegative time. The jump sum
over `(0, t]` is right-continuous in `t` on a window carrying an integrable jump coefficient and a
jump diffusion has almost surely càdlàg paths, so the identity extends from the nonnegative
rationals to all of `[0, ∞)` on a single set of full measure, for any modification of the vector
Itô process whose paths are right-continuous.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.tendsto_jumpSum_nhdsWithin_Ioi` — right-continuity in time of
  the pathwise jump sum.
* `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_of_ae_rat` — two almost surely right-continuous
  processes agreeing almost surely at each nonnegative rational time agree almost surely at every
  nonnegative time.
* `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_add_jumpSum` — the finite-activity splitting,
  almost surely at all nonnegative times simultaneously.
* `LevyStochCalc.Ito.JumpSplitting.jumpSum_eq_of_measure_zero` — the jump sum is constant across a
  window carrying no mass of the random measure.
* `LevyStochCalc.Ito.JumpSplitting.add_shift_eq_of_ae_forall` — the splitting written as a path
  translated by a shift held fixed strictly between consecutive members of a chain of times.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpSplitting

universe u v

section Rationals

end Rationals

section Upgrade

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

end Upgrade

section Setup

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

section AllTimes

variable (X : Setting.JumpDiffusion W N coeffs x₀) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
  (hσm : ∀ (i : Fin n) (j : Fin d),
    Measurable (Function.uncurry fun ω s => coeffs.σ s (X.X s ω) i j))
  (hσp : ∀ (i : Fin n) (j : Fin d),
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (X.X s ω) i j)
  (hσq : ∀ (i : Fin n) (j : Fin d) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.σ s (X.X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (hγm : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i)
  (hγp : ∀ i : Fin n,
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (X.X s ω) e i)
  (hγq : ∀ (i : Fin n) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

end AllTimes

theorem _root_.LevyStochCalc.Ito.JumpSplitting.add_shift_eq_of_ae_forall {X : Setting.JumpDiffusion W N coeffs x₀} {A : Set E}
    {V : ℝ → Ω → Fin n → ℝ}
    (hsplit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      X.X t ω i = V t ω i + jumpSum X A t ω i)
    {σ : ℕ → Ω → WithTop ℝ} {c : ℕ → Ω → Fin n → ℝ}
    (h0 : ∀ ω, σ 0 ω = ((0 : ℝ) : WithTop ℝ))
    (hmono : ∀ (k : ℕ) (ω : Ω), σ k ω ≤ σ (k + 1) ω)
    (hc : ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), σ k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < σ (k + 1) ω → ∀ i : Fin n, jumpSum X A s ω i = c k ω i) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), σ k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < σ (k + 1) ω → V s ω + c k ω = X.X s ω := by sorry
