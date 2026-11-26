-- Prove2me | Theorems.Thm_Malliavin_exists_representative_predictableDerivative_condExp_of_condExp_leftContinuous
-- name    : Malliavin.exists_representative_predictableDerivative_condExp_of_condExp_leftContinuous
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:27:43.105843+00:00
-- url     : https://prove2.me/theorems/bd4e5687-5211-46b6-bf69-86f7af0747d5
-- title:
--   Malliavin: exists representative predictable Derivative cond Exp of cond Exp left Continuous
-- statement:
--   Variant of the textbook identification assuming left-continuity only at the level of
--   conditional expectations (`E[· | 𝓕_{t⁻}] =ᵐ E[· | 𝓕 t]` for integrable integrands), which is
--   the form provable modulo `P`-null sets.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L809-L822
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L809-L822

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable {B : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}

theorem Malliavin.exists_representative_predictableDerivative_condExp_of_condExp_leftContinuous
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P)
    (hlc : ∀ t : ℝ≥0, 0 < t → ∀ X : W → ℝ, Integrable X P →
      P[X | filtrationPred 𝓕 t] =ᵐ[P] P[X | 𝓕 t]) :
    ∃ G : ℝ≥0 × W → ℝ,
      StronglyMeasurable[𝓕.predictable] G ∧
      (predictableDerivative C F : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] G ∧
      ∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
        (fun ω ↦ G (t, ω)) =ᵐ[P]
          P[(fun ω ↦ (C.timeDerivative (mderivD12 P F)) (t, ω)) | 𝓕 t] := by sorry
