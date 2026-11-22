-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpSplitting_ae_exists_atomEnum_jump_eq_gamma_add_remainder
-- name    : LevyStochCalc.Ito.JumpSplitting.ae_exists_atomEnum_jump_eq_gamma_add_remainder
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T10:13:48.40418+00:00
-- url     : https://prove2.me/theorems/bc244197-6b8a-48db-828f-1ea44a56e2fe
-- title:
--   ae exists atomEnum jump eq gamma add remainder
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpSplitting.ae_exists_atomEnum_jump_eq_gamma_add_remainder` is extracted from `LevyStochCalc.Ito.JumpSplittingRemainderDecomposition`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_AtomJumpRelation_F001
import Definitions.Def_LevyStochCalc_Ito_TruncatedContinuousPart_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The splitting of a path with remainder

A path satisfying the jump-diffusion integral equation is, at every nonnegative time, the sum of
a vector Itô process with diffusion `σ` and drift `continuousDriftLeftAt`, the pathwise sum of
the jumps carried by a mark set of finite intensity and the compensated integral of the
left-limit jump coefficient cut to the complement of that set — the *remainder* — so that across
an arrival time carrying a mark of the set the path jumps by the jump coefficient read at its
left limit plus the jump of the remainder.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.eq_vectorItoProcess_add_jumpSumLeftAt_add_remainder_of_path`
  — the splitting with remainder at a fixed nonnegative time.
* `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_add_jumpSumLeftAt_add_remainder_of_path` — the
  same identity almost surely at all nonnegative times.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, Theorem 4.4.7, step (II).
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpSplitting

open LevyStochCalc.Poisson.Compensated

universe u v

section Remainder

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  (coeffs : Setting.JumpDiffusionCoeffs n d E)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (Xp : ℝ → Ω → Fin n → ℝ)
  (x₀ : Fin n → ℝ) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
  (hσm : ∀ (i : Fin n) (j : Fin d),
    Measurable (Function.uncurry fun ω s => coeffs.σ s (Xp s ω) i j))
  (hσp : ∀ (i : Fin n) (j : Fin d),
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (Xp s ω) i j)
  (hσq : ∀ (i : Fin n) (j : Fin d) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.σ s (Xp s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (hγm : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Xp p.2.1 p.1) p.2.2 i)
  (hγp : ∀ i : Fin n,
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (Xp s ω) e i)
  (hγq : ∀ (i : Fin n) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (Xp s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  (hγmL : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E =>
    coeffs.γ p.2.1 (leftLimPathAt Xp p.2.1 p.1) p.2.2 i)
  (hγpL : ∀ i : Fin n, Probability.MarkedProgressivelyMeasurable ℱ
    fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i)
  (hγqL : ∀ (i : Fin n) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (leftLimPathAt Xp s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

end Remainder

section JumpWithRemainder

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}

theorem _root_.LevyStochCalc.Ito.JumpSplitting.ae_exists_atomEnum_jump_eq_gamma_add_remainder
    (coeffs : Setting.JumpDiffusionCoeffs n d E)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (Xp : ℝ → Ω → Fin n → ℝ) (A : Set E) (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ)
    (V : ℝ → Ω → Fin n → ℝ) (hVc : ∀ᵐ ω ∂P, Continuous fun t => V t ω)
    (R : Fin n → ℝ → Ω → ℝ)
    (hRl : ∀ᵐ ω ∂P, ∀ (i : Fin n) (t : ℝ), ∃ L : ℝ, Tendsto (fun s => R i s ω) (𝓝[<] t) (𝓝 L))
    (hsplit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Xp t ω i = V t ω i + jumpSumLeftAt coeffs N Xp A t ω i + R i t ω) :
    ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E), StrictMono θ ∧
      (∀ j, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A) ∧
      (∀ g : ℝ × E → ℝ,
        ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j)) ∧
      ∀ (j : Fin K) (i : Fin n),
        Xp (θ j) ω i
          = leftLimPathAt Xp (θ j) ω i + coeffs.γ (θ j) (leftLimPathAt Xp (θ j) ω) (ε j) i
            + (R i (θ j) ω - Function.leftLim (fun s => R i s ω) (θ j)) := by sorry
