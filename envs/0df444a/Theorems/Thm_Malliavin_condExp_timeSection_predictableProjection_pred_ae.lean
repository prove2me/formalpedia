-- Prove2me | Theorems.Thm_Malliavin_condExp_timeSection_predictableProjection_pred_ae
-- name    : Malliavin.condExp_timeSection_predictableProjection_pred_ae
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:27:38.647701+00:00
-- url     : https://prove2.me/theorems/f1a80891-773c-444e-aa6b-d0a630c69287
-- title:
--   Malliavin: cond Exp time Section predictable Projection pred ae
-- statement:
--   **Sections of the predictable projection are conditional expectations given the strict
--   past**: for almost every `t > 0`, with a null set independent of everything else,
--
--     `E[(Π U) (t, ·) | 𝓕_{t⁻}] =ᵐ[P] E[U (t, ·) | 𝓕_{t⁻}]`,
--
--   where `𝓕_{t⁻} = ⨆_{s < t} 𝓕 s`.  Since a suitable representative of `Π U` has
--   `𝓕_{t⁻}`-measurable sections, this is the textbook identification of the predictable
--   projection; only left-continuity `𝓕_{t⁻} = 𝓕 t` of the filtration separates it from
--   `E[U (t, ·) | 𝓕 t]`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L582-L652
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L582-L652

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
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.condExp_timeSection_predictableProjection_pred_ae
    [SecondCountableTopology (RandomL2 P)] (U : TimeProcessL2 P) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
      P[(fun ω ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω)) | filtrationPred 𝓕 t]
        =ᵐ[P] P[(fun ω ↦ U (t, ω)) | filtrationPred 𝓕 t] := by sorry
