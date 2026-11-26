-- Prove2me | Theorems.Thm_Malliavin_predictableProjection_ae_eq_timewiseCondExpKernel
-- name    : Malliavin.predictableProjection_ae_eq_timewiseCondExpKernel
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:42:49.775806+00:00
-- url     : https://prove2.me/theorems/4795fe2b-5795-5cd6-bcb0-f732ebe72e63
-- title:
--   Malliavin: predictable Projection ae eq timewise Cond Exp Kernel
-- statement:
--   If the pointwise timewise-kernel candidate is jointly predictably measurable, then it is a
--   representative of the product-space predictable projection.  Its product-`L²` bound follows from
--   `memLp_timewiseCondExpKernelRepresentative`.
--
--   Joint predictability is not established here for the natural Brownian filtration.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimewiseCondExp.lean#L227-L246
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimewiseCondExp.lean#L227-L246

import Definitions.Def_Malliavin_NaturalItoDuality
import Mathlib.Probability.Kernel.Condexp
import Definitions.Def_Malliavin_TimewiseCondExp
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]

theorem Malliavin.predictableProjection_ae_eq_timewiseCondExpKernel
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (U : TimeProcessL2 P)
    (hpred : AEStronglyMeasurable[𝓕.predictable]
      (timewiseCondExpKernelRepresentative 𝓕 U)
      (nonnegativeLebesgueMeasure.prod P)) :
    (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) =ᵐ[
      nonnegativeLebesgueMeasure.prod P]
        timewiseCondExpKernelRepresentative 𝓕 U := by sorry
