-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_predictableDerivative_ae_eq_integral_globalPredictableSectionKernel
-- name    : Malliavin.ClarkOconeFamily.predictableDerivative_ae_eq_integral_globalPredictableSectionKernel
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:43:30.964659+00:00
-- url     : https://prove2.me/theorems/a6c11268-c3dd-505a-b0ed-82a6dd24644e
-- title:
--   Clark Ocone Family: predictable Derivative ae eq integral global Predictable Section Kernel
-- statement:
--   **The Clark--Ocone integrand through one kernel**: for any Clark--Ocone family, the
--   integrand `predictableDerivative C F` is, almost everywhere for the product measure, the
--   integral of the time section of the Malliavin time derivative against the single jointly
--   predictable Markov kernel:
--
--     `(Dₜ F)_pred (t, ω) = ∫ y, (Dₜ F) (t, y) ∂globalPredictableSectionKernel P 𝓕 (t, ω)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/KernelIdentification.lean#L594-L603
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/KernelIdentification.lean#L594-L603

import Definitions.Def_Malliavin_PredictableKernel
import Definitions.Def_Malliavin_TimewiseCondExp
import Definitions.Def_Malliavin_NaturalFiltrationLeftContinuous
import Mathlib.MeasureTheory.Function.Floor
import Definitions.Def_Malliavin_KernelIdentification
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

theorem Malliavin.ClarkOconeFamily.predictableDerivative_ae_eq_integral_globalPredictableSectionKernel
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕) (F : D12 P) :
    (predictableDerivative C F : ℝ≥0 × W → ℝ)
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        fun p ↦ ∫ y, (C.timeDerivative (mderivD12 P F)) (p.1, y)
          ∂globalPredictableSectionKernel P 𝓕 p := by sorry
