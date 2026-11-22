-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpSplitting_ae_exists_atomEnum_jump_eq_gamma_of_sdeData
-- name    : LevyStochCalc.Ito.JumpSplitting.ae_exists_atomEnum_jump_eq_gamma_of_sdeData
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T10:17:24.930155+00:00
-- url     : https://prove2.me/theorems/4987596f-8f09-45d8-8cec-f7c419893190
-- title:
--   ae exists atomEnum jump eq gamma of sdeData
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpSplitting.ae_exists_atomEnum_jump_eq_gamma_of_sdeData` is extracted from `LevyStochCalc.Ito.JumpSplittingRemainderVanishing`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_AtomJumpRelation_F001
import Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F000
import Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F001
import Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F002
import Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F004
import Definitions.Def_LevyStochCalc_Ito_TruncatedContinuousPart_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Vanishing remainders and the jump of a solution

Along a subsequence of the spanning sets of the intensity the compensated integrals of a finite
family of integrands cut to the complements of those sets vanish uniformly on every bounded
window, by Doob's `L²` maximal inequality against the Itô–Lévy isometry; passing to such a
subsequence in the splitting with remainder, the jump of a jump diffusion across an arrival time
carrying a mark of a spanning set is exactly the jump coefficient read at the left limit there.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.ae_exists_atomEnum_jump_eq_gamma_of_sdeData` — the jump of a
  solution across an arrival time.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, Theorem 4.4.7, step (II).
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpSplitting

open LevyStochCalc.Poisson.Compensated

universe u v

section Uniform

open LevyStochCalc.Probability

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

end Uniform

section Solution

open LevyStochCalc.Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ} {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}
  {X : Setting.JumpDiffusion W N coeffs x₀}

theorem _root_.LevyStochCalc.Ito.JumpSplitting.ae_exists_atomEnum_jump_eq_gamma_of_sdeData (S : BigJump.SdeData X)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ 0 ≤ S.ℱ t)
    (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμp : ∀ i : Fin n,
      Probability.ProgressivelyMeasurable S.ℱ fun ω s => coeffs.μ s (X.X s ω) i)
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hγmL : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E =>
      coeffs.γ p.2.1 (leftLimPathAt X.X p.2.1 p.1) p.2.2 i)
    (hγpL : ∀ i : Fin n, Probability.MarkedProgressivelyMeasurable S.ℱ
      fun ω s e => coeffs.γ s (leftLimPathAt X.X s ω) e i)
    (hγqL : ∀ (i : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (leftLimPathAt X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hpredL : ∀ i : Fin n, Probability.MarkedPredictable S.ℱ ν
      (JumpFormula.zeroExtPos fun ω s e => coeffs.γ s (leftLimPathAt X.X s ω) e i))
    (j₀ : ℕ) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E), StrictMono θ ∧
      (∀ j, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ spanningSets ν j₀) ∧
      (∀ g : ℝ × E → ℝ, ∫ p in Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν j₀, g p ∂(N.N ω)
        = ∑ j : Fin K, g (θ j, ε j)) ∧
      ∀ j : Fin K,
        X.X (θ j) ω
          = leftLimPathAt X.X (θ j) ω + coeffs.γ (θ j) (leftLimPathAt X.X (θ j) ω) (ε j) := by sorry
