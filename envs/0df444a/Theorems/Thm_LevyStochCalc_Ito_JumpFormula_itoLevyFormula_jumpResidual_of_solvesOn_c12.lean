-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_itoLevyFormula_jumpResidual_of_solvesOn_c12
-- name    : LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_solvesOn_c12
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T13:20:10.475264+00:00
-- url     : https://prove2.me/theorems/bb292c1b-d4eb-450c-92c4-7dceb0589739
-- title:
--   itoLevyFormula jumpResidual of solvesOn c12
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_solvesOn_c12` is extracted from `LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionMainC12`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionIntegrandsC12_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionMain_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô–Lévy formula at bounded derivatives from the solution data, for `C^{1,2}` state
functions

For regular Lipschitz coefficients and a filtration satisfying the usual conditions, a `C^{1,2}`
state function with bounded time derivative, gradient and Hessian satisfies the Itô–Lévy formula
along a jump diffusion that solves the equation on every window, that carries SDE data and has
left limits at every sample point and every time, or that carries SDE data alone: its increment
is the drift integral, the Brownian integral of `(∇u)ᵀσ`, the compensated integral of
`u(x + γ) − u(x)` and the compensator-drift integral. Every admissibility input of the two
stochastic integrals is derived from the solution data and the coefficient regularity.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_solvesOn_c12` — the residual
  form along a solution of the equation on every window, for a `C^{1,2}` state function.
* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_sdeData_of_leftLim_c12` — the
  residual form along a solution with left limits at every sample point and every time.
* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_sdeData_c12` — the residual form
  along any jump diffusion carrying SDE data.
* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_of_boundedDerivs_c12` — the four-term form.
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

theorem _root_.LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_solvesOn_c12 [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hReg : coeffs.IsRegular ν) {L : ℝ} (hLip : coeffs.IsLipschitz ν L) (x₀ : Fin n → ℝ)
    (u : ℝ → (Fin n → ℝ) → ℝ) (hu : IsC12 u)
    {K₀ K₁ K₂ : ℝ} (hK₀ : ∀ s x, |timeDeriv u s x| ≤ K₀)
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁) (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂)
    (T : ℝ) (hT : 0 < T) :
    ∃ (X : JumpDiffusion W N coeffs x₀)
      (hsol : ∀ T' : ℝ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ X.X T')
      (hXa : ∀ i : Fin n, ProgressivelyMeasurable ℱ fun ω s => X.X s ω i),
      (∀ (ω : Ω) (t : ℝ), Tendsto (fun s => X.X s ω) (𝓝[>] t) (𝓝 (X.X t ω))
          ∧ ∀ j : Fin n, ∃ L : ℝ, Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
      ∧ ∀ᵐ ω ∂P,
        (u T (X.X T ω) - u 0 (X.X 0 ω)
          - (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
          - MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
              (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
              (fun j => measurable_diffusionIntegrand_path_c12 hu hReg.2.1 X.measurable_path j)
              (fun j => progressivelyMeasurable_diffusionIntegrand_path_c12 hu hReg.2.1 hXa j)
              (fun j _ hT' => lintegral_sq_diffusionIntegrand_path_lt_top hK₁
                (hsol 0).h_σ_meas (hsol 0).h_σ_sq j hT') T ω)
          = LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
              (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
              (measurable_jumpIncrement_path_c12 hu hReg.2.2.1 X.measurable_path)
              (markedProgressivelyMeasurable_jumpIncrement_path_c12 hu hReg.2.2.1 hXa)
              (fun _ hT' => lintegral_sq_jumpIncrement_path_lt_top_c12 hu hK₁ (hsol 0).h_γ_meas
                (hsol 0).h_γ_sq hT') T ω
          + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
              compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν := by sorry
