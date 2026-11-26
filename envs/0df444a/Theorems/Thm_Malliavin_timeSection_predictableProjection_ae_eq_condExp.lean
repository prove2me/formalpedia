-- Prove2me | Theorems.Thm_Malliavin_timeSection_predictableProjection_ae_eq_condExp
-- name    : Malliavin.timeSection_predictableProjection_ae_eq_condExp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:20:07.311935+00:00
-- url     : https://prove2.me/theorems/2ca2a007-1e44-455e-84f7-44e6fbcbfe20
-- title:
--   Malliavin: time Section predictable Projection ae eq cond Exp
-- statement:
--   **Textbook identification of the predictable projection.**  Any predictable strongly
--   measurable representative `G` of `predictableProjection 𝓕 U` satisfies, for almost every
--   `t > 0`,
--
--     `G (t, ·) =ᵐ[P] E[U (t, ·) | 𝓕_{t⁻}]`,
--
--   a literal pointwise conditional-expectation formula for the sections.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L695-L714
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L695-L714

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

theorem Malliavin.timeSection_predictableProjection_ae_eq_condExp
    [SecondCountableTopology (RandomL2 P)] (U : TimeProcessL2 P)
    {G : ℝ≥0 × W → ℝ} (hG : StronglyMeasurable[𝓕.predictable] G)
    (hGae : (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ)
      =ᵐ[nonnegativeLebesgueMeasure.prod P] G) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
      (fun ω ↦ G (t, ω)) =ᵐ[P] P[(fun ω ↦ U (t, ω)) | filtrationPred 𝓕 t] := by sorry
