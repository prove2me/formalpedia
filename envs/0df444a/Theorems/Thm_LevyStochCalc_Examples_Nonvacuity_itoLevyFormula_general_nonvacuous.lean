-- Prove2me | Theorems.Thm_LevyStochCalc_Examples_Nonvacuity_itoLevyFormula_general_nonvacuous
-- name    : LevyStochCalc.Examples.Nonvacuity.itoLevyFormula_general_nonvacuous
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T12:51:19.753534+00:00
-- url     : https://prove2.me/theorems/499f0a98-73c1-4f74-bc11-526c1f1819b6
-- title:
--   itoLevyFormula general nonvacuous
-- statement:
--   The source theorem `LevyStochCalc.Examples.Nonvacuity.itoLevyFormula_general_nonvacuous` is extracted from `NonvacuityItoLevy`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_AugmentedFiltration_F000
import Definitions.Def_LevyStochCalc_Brownian_AugmentedFiltration_F001
import Definitions.Def_LevyStochCalc_Brownian_Filtered_F000
import Definitions.Def_LevyStochCalc_Brownian_MultidimIto_F000
import Definitions.Def_LevyStochCalc_Driver_Existence_F000
import Definitions.Def_LevyStochCalc_Driver_Joint_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionIntegrands_F000
import Definitions.Def_LevyStochCalc_Ito_PicardWellPosed_F000
import Definitions.Def_LevyStochCalc_Ito_SdeDataOfSolvesOn_F000
import Definitions.Def_LevyStochCalc_Poisson_Compensated_F000
import Definitions.Def_LevyStochCalc_Poisson_Filtered_F000
import Definitions.Def_LevyStochCalc_Poisson_PredictableRepresentation_F001
import Definitions.Def_NonvacuityItoLevy_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A jump diffusion satisfying the hypotheses of the Itô–Lévy formula

The scalar jump diffusion `dX_t = dW_t + ∫_ℝ e Ñ(dt, de)` with `X_0 = 0`, driven by a
one-dimensional Brownian motion and a Poisson random measure of intensity `dt ⊗ δ_1` on
`[0, ∞) × ℝ`, together with the state function `u(t, x) = x₀²` on the horizon `[0, 1]`.

The coefficients `μ = 0`, `σ = 1`, `γ(s, x, e) = e` are regular and Lipschitz with constant
`0`, so the SDE has a solution, and `u` is `C²` with gradient `∇u(s, x) = 2x₀`, diffusion
integrand `(∇u)ᵀσ = 2x₀`, jump increment `u(x + e) − u(x) = 2ex₀ + e²` and compensator drift
`u(x + e) − u(x) − e∇u(x) = e²`. The derived energies are finite because the solution has a
finite `S²` norm on every window, and the compensator drift is the constant `1`.

The gradient of `u` is unbounded, so `u` lies outside the range of the Itô–Lévy formula for a
state function with bounded first and second derivatives.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.JumpFormula

/-! ### The model -/

/-! ### Regularity of the coefficients -/

/-! ### The derivatives of `u(t, x) = x₀²` -/

/-! ### Finite energy along an `S²`-bounded path -/

section Energy

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end Energy

/-! ### The witness -/

open LevyStochCalc.Brownian.Multidim (MultidimBrownianMotion)
open LevyStochCalc.Poisson (PoissonRandomMeasure)
open LevyStochCalc.Ito.BigJump (SdeData)

theorem _root_.LevyStochCalc.Examples.Nonvacuity.itoLevyFormula_general_nonvacuous :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (W : MultidimBrownianMotion P 1) (N : PoissonRandomMeasure P jumpIntensity)
      (X : JumpDiffusion W N coeffs (0 : Fin 1 → ℝ)) (S : SdeData X)
      (_ : S.ℱ.IsRightContinuous)
      (_hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ 0 ≤ S.ℱ t)
      (_hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
      (_hμmeas : Measurable (Function.uncurry coeffs.μ))
      (hσmeas : Measurable (Function.uncurry coeffs.σ))
      (hγmeas : Measurable fun q : ℝ × (Fin 1 → ℝ) × ℝ => coeffs.γ q.1 q.2.1 q.2.2)
      (_hμq : ∀ (i : Fin 1) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
      (hu : ContDiff ℝ 2 (Function.uncurry uSq))
      (_hT : (0 : ℝ) < 1)
      (h_sigmaGrad_sq : ∀ j : Fin 1, ∀ T' : ℝ, 0 < T' →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          (‖diffusionIntegrand uSq coeffs.σ s (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
      (h_jumpInt_sq : ∀ T' : ℝ, 0 < T' →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
          (‖uSq s (X.X s ω + coeffs.γ s (X.X s ω) e) - uSq s (X.X s ω)‖₊ : ℝ≥0∞) ^ 2
            ∂jumpIntensity ∂volume ∂P < ⊤)
      (_h_compDrift_int : ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc (0 : ℝ) 1, ∫⁻ e,
        (‖compensatorDriftIntegrand uSq coeffs.γ s (X.X s ω) e‖₊ : ℝ≥0∞)
          ∂jumpIntensity ∂volume < ⊤),
      ∀ᵐ ω ∂P,
        uSq 1 (X.X 1 ω) - uSq 0 (X.X 0 ω)
          = (∫ s in Set.Icc (0 : ℝ) 1, driftIntegrand uSq coeffs s (X.X s ω))
            + MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
                (fun s ω => diffusionIntegrand uSq coeffs.σ s (X.X s ω))
                (fun j => measurable_diffusionIntegrand_path hu hσmeas X.measurable_path j)
                (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hσmeas S.X_prog j)
                h_sigmaGrad_sq 1 ω
            + LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
                (fun ω' s e => uSq s (X.X s ω' + coeffs.γ s (X.X s ω') e) - uSq s (X.X s ω'))
                (measurable_jumpIncrement_path hu hγmeas X.measurable_path)
                (markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas S.X_prog)
                h_jumpInt_sq 1 ω
            + ∫ s in Set.Icc (0 : ℝ) 1, ∫ e,
                compensatorDriftIntegrand uSq coeffs.γ s (X.X s ω) e ∂jumpIntensity := by sorry
