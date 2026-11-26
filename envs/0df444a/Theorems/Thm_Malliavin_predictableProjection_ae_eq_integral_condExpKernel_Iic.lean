-- Prove2me | Theorems.Thm_Malliavin_predictableProjection_ae_eq_integral_condExpKernel_Iic
-- name    : Malliavin.predictableProjection_ae_eq_integral_condExpKernel_Iic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:24:08.305888+00:00
-- url     : https://prove2.me/theorems/5ab531d7-d8b0-4324-af20-dd4b9f5b7ed9
-- title:
--   Malliavin: predictable Projection ae eq integral cond Exp Kernel Iic
-- statement:
--   On a finite time horizon, the global predictable `L²` projection is represented pointwise by
--   Mathlib's conditional-expectation kernel for the predictable σ-algebra on the product space.
--
--   The integration variable `q` still ranges over `ℝ≥0 × W`; this theorem deliberately makes no
--   claim that the kernel is the fixed-time kernel `condExpKernel P (𝓕 p.1)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableKernel.lean#L146-L204
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableKernel.lean#L146-L204

import Definitions.Def_Malliavin_ClarkOcone
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Composition.MapComap
import Definitions.Def_Malliavin_PredictableKernel
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]

theorem Malliavin.predictableProjection_ae_eq_integral_condExpKernel_Iic
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (U : TimeProcessL2 P) (T : ℝ≥0) :
    (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ)
      =ᵐ[finiteHorizonProductMeasure P T]
        fun p => ∫ q, U q
          ∂condExpKernel (finiteHorizonProductMeasure P T) 𝓕.predictable p := by sorry
