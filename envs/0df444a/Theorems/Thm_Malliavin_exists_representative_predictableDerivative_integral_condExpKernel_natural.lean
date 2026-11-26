-- Prove2me | Theorems.Thm_Malliavin_exists_representative_predictableDerivative_integral_condExpKernel_natural
-- name    : Malliavin.exists_representative_predictableDerivative_integral_condExpKernel_natural
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:56:45.778903+00:00
-- url     : https://prove2.me/theorems/706d07ad-f06a-48d3-881c-ef5eecab469e
-- title:
--   Malliavin: exists representative predictable Derivative integral cond Exp Kernel natural
-- statement:
--   Kernel form of the textbook Clark--Ocone integrand: the representative is the integral of
--   the time section of the Malliavin derivative against `condExpKernel P (𝓕 t)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalFiltrationLeftContinuous.lean#L141-L157
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalFiltrationLeftContinuous.lean#L141-L157

import Definitions.Def_Malliavin_PointwiseCondExp
import Definitions.Def_Malliavin_NaturalFiltrationLeftContinuous
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable {B : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}

theorem Malliavin.exists_representative_predictableDerivative_integral_condExpKernel_natural
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) :
    ∃ G : ℝ≥0 × W → ℝ,
      StronglyMeasurable[𝓕.predictable] G ∧
      (predictableDerivative C F : ℝ≥0 × W → ℝ)
        =ᵐ[nonnegativeLebesgueMeasure.prod P] G ∧
      ∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
        (fun w ↦ G (t, w)) =ᵐ[P]
          fun w ↦ ∫ y, (C.timeDerivative (mderivD12 P F)) (t, y)
            ∂condExpKernel P (𝓕 t) w := by sorry
