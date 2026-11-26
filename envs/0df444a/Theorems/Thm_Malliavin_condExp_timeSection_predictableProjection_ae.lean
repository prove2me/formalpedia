-- Prove2me | Theorems.Thm_Malliavin_condExp_timeSection_predictableProjection_ae
-- name    : Malliavin.condExp_timeSection_predictableProjection_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:27:20.176518+00:00
-- url     : https://prove2.me/theorems/965a2eef-2af6-4fa5-a327-95417e83078b
-- title:
--   Malliavin: cond Exp time Section predictable Projection ae
-- statement:
--   **Uniform conditional-expectation identification of the sections.**  When the ambient `L²`
--   space is second countable (for instance over a Wiener-generated Gaussian space,
--   `secondCountableTopology_randomL2_of_isWienerGenerated`), for every `a`, for almost every
--   `t > a` — with a null set *independent of any test event* — the conditional expectations given
--   `𝓕 a` of the sections of `Π U` and of `U` coincide:
--
--     `E[(Π U) (t, ·) | 𝓕 a] =ᵐ[P] E[U (t, ·) | 𝓕 a]`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L507-L555
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L507-L555

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

theorem Malliavin.condExp_timeSection_predictableProjection_ae
    [SecondCountableTopology (RandomL2 P)] (U : TimeProcessL2 P) (a : ℝ≥0) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, a < t →
      P[(fun ω ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω)) | 𝓕 a]
        =ᵐ[P] P[(fun ω ↦ U (t, ω)) | 𝓕 a] := by sorry
