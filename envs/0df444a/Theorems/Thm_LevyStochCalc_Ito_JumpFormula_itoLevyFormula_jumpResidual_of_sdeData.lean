-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_itoLevyFormula_jumpResidual_of_sdeData
-- name    : LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_sdeData
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T12:57:11.521021+00:00
-- url     : https://prove2.me/theorems/3817a5f6-1c08-404d-97fc-e0c0bef1297c
-- title:
--   itoLevyFormula jumpResidual of sdeData
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_sdeData` is extracted from `LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionMain`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionIntegrands_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionRepresentative_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô–Lévy formula at bounded derivatives, from the solution data

For regular Lipschitz coefficients and a filtration satisfying the usual conditions, a `C²` state
function with bounded time derivative, gradient and Hessian satisfies the Itô–Lévy formula along
a jump diffusion that solves the equation on every window, that carries SDE data and has left
limits at every sample point and every time, or that carries SDE data alone: its increment is the
drift integral, the Brownian integral of `(∇u)ᵀσ`, the compensated integral of `u(x + γ) − u(x)`
and the compensator-drift integral. Every admissibility input of the two stochastic integrals is
derived from the solution data and the coefficient regularity; `multidimIntegral_congr_ae`
transports the Brownian integral between vector integrands agreeing almost everywhere on a
window.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.Picard LevyStochCalc.Ito.BigJump
  LevyStochCalc.Probability

universe u v

section Main

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (coeffs : JumpDiffusionCoeffs n d E)

theorem _root_.LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_sdeData (x₀ : Fin n → ℝ)
    (X : JumpDiffusion W N coeffs x₀) (S : LevyStochCalc.Ito.BigJump.SdeData X)
    [S.ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ 0 ≤ S.ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    (hμmeas : Measurable (Function.uncurry coeffs.μ))
    (hσmeas : Measurable (Function.uncurry coeffs.σ))
    (hγmeas : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hμq : ∀ (i : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (u : ℝ → (Fin n → ℝ) → ℝ) (hu : ContDiff ℝ 2 (Function.uncurry u))
    {K₀ K₁ K₂ : ℝ} (hK₀ : ∀ s x, |timeDeriv u s x| ≤ K₀)
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁) (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂)
    (T : ℝ) (hT : 0 < T) :
    ∀ᵐ ω ∂P,
      (u T (X.X T ω) - u 0 (X.X 0 ω)
        - (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
        - MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
            (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
            (fun j => measurable_diffusionIntegrand_path hu hσmeas X.measurable_path j)
            (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hσmeas S.X_prog j)
            (fun j _ hT' => lintegral_sq_diffusionIntegrand_path_lt_top hK₁
              S.σ_meas S.σ_sq j hT') T ω)
      = LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
          (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
          (measurable_jumpIncrement_path hu hγmeas X.measurable_path)
          (markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas S.X_prog)
          (fun _ hT' => lintegral_sq_jumpIncrement_path_lt_top hu hK₁ S.γ_meas S.γ_sq hT') T ω
        + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
            compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν := by sorry
