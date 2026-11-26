-- Prove2me | Theorems.Thm_Malliavin_exists_representative_predictableDerivative_condExp_of_leftContinuous
-- name    : Malliavin.exists_representative_predictableDerivative_condExp_of_leftContinuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:55:16.492965+00:00
-- url     : https://prove2.me/theorems/5e4b6090-1243-51ba-9858-45c6a833b9f3
-- title:
--   Malliavin: exists representative predictable Derivative cond Exp of left Continuous
-- statement:
--   **Textbook Clark--Ocone integrand under left-continuity.**  If the filtration is
--   left-continuous at positive times (`𝓕_{t⁻} = 𝓕 t`), the Clark--Ocone integrand has a
--   predictable representative `G` with, for almost every `t > 0`,
--
--     `G (t, ·) =ᵐ[P] E[(Dₜ F) (t, ·) | 𝓕 t]`,
--
--   which is the literal textbook `E[Dₜ F | 𝓕ₜ]`.  Left-continuity of the natural Brownian
--   filtration is the single remaining input.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L791-L804
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L791-L804

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

theorem Malliavin.exists_representative_predictableDerivative_condExp_of_leftContinuous
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P)
    (hlc : ∀ t : ℝ≥0, 0 < t → filtrationPred 𝓕 t = 𝓕 t) :
    ∃ G : ℝ≥0 × W → ℝ,
      StronglyMeasurable[𝓕.predictable] G ∧
      (predictableDerivative C F : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] G ∧
      ∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
        (fun ω ↦ G (t, ω)) =ᵐ[P]
          P[(fun ω ↦ (C.timeDerivative (mderivD12 P F)) (t, ω)) | 𝓕 t] := by sorry
