-- Prove2me | Theorems.Thm_Malliavin_exists_representative_predictableDerivative_condExp_natural
-- name    : Malliavin.exists_representative_predictableDerivative_condExp_natural
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:27:42.282412+00:00
-- url     : https://prove2.me/theorems/ea08b71e-7b06-549d-a445-a12c4a98c4ed
-- title:
--   Malliavin: exists representative predictable Derivative cond Exp natural
-- statement:
--   **Literal textbook Clark--Ocone integrand.**  For every `F ∈ 𝔻₁,₂`, the predictable
--   derivative has a predictable representative whose section is `E[DₜF | 𝓕_t]` for almost every
--   positive time.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalFiltrationLeftContinuous.lean#L126-L137
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalFiltrationLeftContinuous.lean#L126-L137

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

theorem Malliavin.exists_representative_predictableDerivative_condExp_natural
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) :
    ∃ G : ℝ≥0 × W → ℝ,
      StronglyMeasurable[𝓕.predictable] G ∧
      (predictableDerivative C F : ℝ≥0 × W → ℝ)
        =ᵐ[nonnegativeLebesgueMeasure.prod P] G ∧
      ∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
        (fun w ↦ G (t, w)) =ᵐ[P]
          P[(fun w ↦ (C.timeDerivative (mderivD12 P F)) (t, w)) | 𝓕 t] := by sorry
