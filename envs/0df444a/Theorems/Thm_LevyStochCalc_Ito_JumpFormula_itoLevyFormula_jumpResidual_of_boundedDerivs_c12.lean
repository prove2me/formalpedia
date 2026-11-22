-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_itoLevyFormula_jumpResidual_of_boundedDerivs_c12
-- name    : LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_boundedDerivs_c12
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T12:54:26.548982+00:00
-- url     : https://prove2.me/theorems/fb562d1f-c239-49ee-a7dd-59b621b19825
-- title:
--   itoLevyFormula jumpResidual of boundedDerivs c12
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_boundedDerivs_c12` is extracted from `LevyStochCalc.Ito.ItoLevyBoundedDerivsC12`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsC12Limits_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô–Lévy formula for a `C^{1,2}` state function with bounded derivatives

The Itô–Lévy identity along a jump diffusion for a state function that is once continuously
differentiable in time and twice continuously differentiable in state, with bounded time
derivative, gradient and Hessian, the class `C^{1,2}` being strictly larger than the class of
functions that are `C²` jointly in time and state. The identity for a jointly `C²` state
function is carried to it by joint mollification: the mollifications of a `C^{1,2}` function are
`C²` jointly in time and state and obey the same three bounds, so the identity holds for each of
them, and every term converges as the outer radii of the bumps tend to `0` — the endpoints and
the two Lebesgue integrals pointwise and by dominated convergence, the Brownian and compensated
integrals in `L²`, hence almost surely along a subsequence along which the identity passes to the
limit.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_boundedDerivs_c12` — the
  canonical residual is the compensated jump integral plus the compensator-drift integral.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section Main

open LevyStochCalc.Ito.BigJump LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

open LevyStochCalc.Ito.IntegralLimit in

theorem _root_.LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_boundedDerivs_c12
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (x₀ : Fin n → ℝ)
    (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀)
    -- Correction 8 (one filtration): the SDE data of `X`, with the usual-conditions shape at
    -- time zero that the truncated paths need.
    (S : LevyStochCalc.Ito.BigJump.SdeData X)
    -- Correction 8 (usual conditions): the filtration of the SDE data is right continuous, so
    -- its right continuation is itself and the two shapes of `hℱ0` are the same statement.
    [S.ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ.rightCont 0 ≤ S.ℱ.rightCont t)
    (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    -- (3) The structure calls its solution adapted but carries no such field.
    (hXadapt : ∀ t : ℝ, Measurable[S.ℱ t] (X.X t))
    -- (3') Statement change: `cadlag_paths` holds almost surely and only on `[0, ∞)`, while the
    -- left limits along which the jump coefficient is read must exist at every sample point and
    -- every time for that reading to be a process at all.
    (hXleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
    -- (5) The drift along the path.
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    -- (5') Statement change: `SdeData` carries no drift field, and progressive measurability of
    -- the drift along the path does not follow from its joint measurability.
    (hμp : ∀ i : Fin n,
      Probability.ProgressivelyMeasurable S.ℱ fun ω s => coeffs.μ s (X.X s ω) i)
    (hμq : ∀ (i : Fin n) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    -- (6) Joint measurability of the jump coefficient.
    (hγmeas : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (u : ℝ → (Fin n → ℝ) → ℝ)
    (hu : IsC12 u)
    -- The bounded derivatives, coordinatewise.
    {K₀ K₁ K₂ : ℝ}
    (hK₀ : ∀ s x, |timeDeriv u s x| ≤ K₀)
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁)
    (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂)
    (T : ℝ) (hT : 0 < T)
    (_h_μ_int : ∀ᵐ ω ∂P, ∀ i : Fin n,
        IntegrableOn (fun s => coeffs.μ s (X.X s ω) i) (Set.Icc (0 : ℝ) T))
    (h_sigmaGrad_meas : ∀ j : Fin d,
        Measurable (Function.uncurry
          (fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j)))
    (h_sigmaGrad_progMeas : ∀ j : Fin d,
        Probability.ProgressivelyMeasurable S.ℱ
          (fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j))
    (h_sigmaGrad_sq : ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          (‖diffusionIntegrand u coeffs.σ s (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P < ⊤)
    (h_jumpInt_meas : Measurable
        (fun (p : Ω × ℝ × E) =>
          (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e)
                          - u s (X.X s ω')) p.1 p.2.1 p.2.2))
    (h_jumpInt_progMeas :
        Probability.MarkedProgressivelyMeasurable S.ℱ
          (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω')))
    (h_jumpInt_sq : ∀ T' : ℝ, 0 < T' →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
          (‖u s (X.X s ω + coeffs.γ s (X.X s ω) e)
              - u s (X.X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (_h_compDrift_int : ∀ᵐ ω ∂P,
        ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e‖₊ : ℝ≥0∞)
            ∂ν ∂volume < ⊤) :
    ∀ᵐ ω ∂P,
      (u T (X.X T ω) - u 0 (X.X 0 ω)
        - (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
        - LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
            W S.ℱ S.isBrownian
            (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
            h_sigmaGrad_meas h_sigmaGrad_progMeas h_sigmaGrad_sq T ω)
        =
        LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
            (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e)
                            - u s (X.X s ω'))
            h_jumpInt_meas h_jumpInt_progMeas h_jumpInt_sq T ω
        + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
            compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν := by sorry
