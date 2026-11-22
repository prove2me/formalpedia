-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_itoLevy_finiteActivity_mixed
-- name    : LevyStochCalc.Ito.JumpFormula.itoLevy_finiteActivity_mixed
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T12:37:54.302323+00:00
-- url     : https://prove2.me/theorems/ca0bce4d-2d07-4bb4-b193-78688c889721
-- title:
--   itoLevy finiteActivity mixed
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.itoLevy_finiteActivity_mixed` is extracted from `LevyStochCalc.Ito.FiniteActivityMixed`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedSteps_F000
import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedSteps_F001
import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedSteps_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The finite-activity Itô–Lévy identity along a truncated path, in the mixed form

Along a càdlàg path `y` that is a continuous vector Itô process plus the left-limit jump sum of
a jump diffusion `X` over a mark set of finite intensity, the increment of a `C²` state function
with bounded derivatives is the mixed drift integral, the Brownian integral of the mixed
diffusion integrand, the compensated integral of the mixed jump increment over the mark set and
the compensator-drift integral over that set. The derivatives of the state function are read
along `y` and the coefficients along `X`.

The proof telescopes Itô's formula for the time-augmented continuous part between consecutive
arrival times of the mark set, identifies the increments across the arrival times with the
atom sum of the mixed jump increment read at the left limits, and identifies that atom sum with
the pathwise form of the compensated integral.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.itoLevy_finiteActivity_mixed`
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability
open LevyStochCalc.Brownian.Ito LevyStochCalc.Brownian.Multidim LevyStochCalc.Ito.BigJump
open LevyStochCalc.Ito.JumpSplitting

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section BrownianSum

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)

end BrownianSum

section Main

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : MultidimBrownianMotion P d} {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}

theorem _root_.LevyStochCalc.Ito.JumpFormula.itoLevy_finiteActivity_mixed
    (S : SdeData X)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ 0 ≤ S.ℱ t)
    (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    (hXadapt : ∀ t : ℝ, Measurable[S.ℱ t] (X.X t))
    (hXleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμp : ∀ i : Fin n,
      Probability.ProgressivelyMeasurable S.ℱ fun ω s => coeffs.μ s (X.X s ω) i)
    (hμq : ∀ (i : Fin n) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hγmeas : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (u : ℝ → (Fin n → ℝ) → ℝ) (hu : ContDiff ℝ 2 (Function.uncurry u))
    {K₀ K₁ K₂ : ℝ}
    (hK₀ : ∀ s x, |timeDeriv u s x| ≤ K₀)
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁)
    (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂)
    (T : ℝ) (hT : 0 < T)
    {B : Set E} (hB : MeasurableSet B) (hBν : ν B ≠ ⊤)
    (y : ℝ → Ω → Fin n → ℝ)
    (hy_m : Measurable (Function.uncurry y))
    (hy_rc : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => y s ω) (𝓝[>] t) (𝓝 (y t ω)))
    (hy_ad : ∀ t : ℝ, Measurable[S.ℱ t] (y t))
    (hy_left : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => y s ω j) (𝓝[<] t) (𝓝 L))
    (V : ℝ → Ω → Fin n → ℝ)
    (hV : IsVectorItoVersion W S.ℱ S.isBrownian
      (fun i j ω s => coeffs.σ s (X.X s ω) i j) S.σ_meas S.σ_prog S.σ_sq (fun _ => x₀)
      (continuousDriftLeftAt coeffs ν X.X B) V)
    (hsplit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      y t ω i = V t ω i + jumpSumLeftAt (coeffs.markCutγ B) N X.X B t ω i)
    (hBm : ∀ j : Fin d, Measurable (Function.uncurry
      fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j))
    (hBp : ∀ j : Fin d, Probability.ProgressivelyMeasurable S.ℱ
      fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j)
    (hBq : ∀ (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hCm : Measurable fun p : Ω × ℝ × E => markCut B
      (fun ω s e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e) p.1 p.2.1 p.2.2)
    (hCp : Probability.MarkedProgressivelyMeasurable S.ℱ (markCut B
      fun ω s e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e))
    (hCq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖markCut B (fun ω s e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e) ω s e‖₊ :
        ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P,
      u T (y T ω) - u 0 (y 0 ω)
        - (∫ s in Set.Icc (0 : ℝ) T, mixedDriftIntegrand u coeffs s (y s ω) (X.X s ω))
        - MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
            (fun s ω => mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω)) hBm hBp hBq T ω
        = stochasticIntegral N S.ℱ S.isPoisson
            (markCut B fun ω s e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e)
            hCm hCp hCq T ω
          + ∫ s in Set.Icc (0 : ℝ) T, ∫ e in B,
              mixedCompensatorDriftIntegrand u coeffs.γ s (y s ω) (X.X s ω) e ∂ν := by sorry
