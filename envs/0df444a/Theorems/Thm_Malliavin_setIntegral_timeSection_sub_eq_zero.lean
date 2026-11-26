-- Prove2me | Theorems.Thm_Malliavin_setIntegral_timeSection_sub_eq_zero
-- name    : Malliavin.setIntegral_timeSection_sub_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:26:37.346052+00:00
-- url     : https://prove2.me/theorems/792fd1a7-7061-4cec-ab4a-a1ff50a0784c
-- title:
--   Malliavin: set Integral time Section sub eq zero
-- statement:
--   A window integral of the section integrals of the difference vanishes on every interval.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L91-L119
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L91-L119

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

theorem Malliavin.setIntegral_timeSection_sub_eq_zero (U : TimeProcessL2 P) {a : ℝ≥0} {A : Set W}
    (hA : MeasurableSet[𝓕 a] A)
    (D : TimeProcessL2 P)
    (hD : (D : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun x ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) x - U x)
    {c d : ℝ≥0} (hac : a ≤ c) :
    ∫ t in Set.Ioc c d, ∫ ω in A, (D : ℝ≥0 × W → ℝ) (t, ω) ∂P
      ∂nonnegativeLebesgueMeasure = 0 := by sorry
