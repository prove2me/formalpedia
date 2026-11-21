-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpSplitting_eq_vectorItoProcess_add_jumpSum
-- name    : LevyStochCalc.Ito.JumpSplitting.eq_vectorItoProcess_add_jumpSum
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:43:00.028191+00:00
-- url     : https://prove2.me/theorems/e2055fd5-3575-4eae-a3b6-1cad8f53cbd2
-- title:
--   eq vectorItoProcess add jumpSum
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpSplitting.eq_vectorItoProcess_add_jumpSum` is extracted from `LevyStochCalc.Ito.JumpSplitting`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpSplitting_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Finite-activity splitting of a jump diffusion

A jump diffusion whose jump coefficient is carried by a mark set of finite intensity is the sum
of a vector Itô process and a pathwise jump sum. The compensated Poisson integral of such a
coefficient is the pathwise integral against the random measure minus the integral against the
reference intensity, and the latter is an absolutely continuous drift, so it can be absorbed into
the drift of the Itô part.

## Main definitions

* `LevyStochCalc.Ito.JumpSplitting.jumpSum` — the pathwise sum of the jumps carried by a mark set
  over a time window.
* `LevyStochCalc.Ito.JumpSplitting.continuousDrift` — the drift of a jump diffusion with the jump
  compensator subtracted.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.eq_vectorItoProcess_add_jumpSum` — at every nonnegative time a
  jump diffusion is almost surely the sum of the vector Itô process with diffusion `σ` and drift
  `continuousDrift`, and the pathwise jump sum.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpSplitting

universe u v

section ENNRealAux

end ENNRealAux

section Comparison

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

end Comparison

section Setup

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

section Regularity

variable (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E) (i : Fin n)

end Regularity

section Splitting

variable (X : Setting.JumpDiffusion W N coeffs x₀) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
  (hσm : ∀ (i : Fin n) (j : Fin d),
    Measurable (Function.uncurry fun ω s => coeffs.σ s (X.X s ω) i j))
  (hσp : ∀ (i : Fin n) (j : Fin d),
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (X.X s ω) i j)
  (hσq : ∀ (i : Fin n) (j : Fin d) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.σ s (X.X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (hγm : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i)
  (hγp : ∀ i : Fin n,
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (X.X s ω) e i)
  (hγq : ∀ (i : Fin n) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

theorem _root_.LevyStochCalc.Ito.JumpSplitting.eq_vectorItoProcess_add_jumpSum
    (hSDE : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      X.X t ω i = x₀ i
        + (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X.X s ω) i)
        + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
            (fun s ω => coeffs.σ s (X.X s ω) i) (fun j => hσm i j) (fun j => hσp i j)
            (fun j => hσq i j) t ω
        + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i) t ω)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hsupp : ∀ (s : ℝ) (x : Fin n → ℝ) (e : E), e ∉ A → coeffs.γ s x e = 0)
    (hpred : ∀ i : Fin n,
      Probability.MarkedPredictable ℱ ν fun ω s e => coeffs.γ s (X.X s ω) e i)
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ∀ i : Fin n,
      X.X t ω i
        = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
            (fun i j ω s => coeffs.σ s (X.X s ω) i j) hσm hσp hσq (fun _ => x₀)
            (continuousDrift X A) t ω i
          + jumpSum X A t ω i := by sorry
