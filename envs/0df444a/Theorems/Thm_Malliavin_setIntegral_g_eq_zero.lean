-- Prove2me | Theorems.Thm_Malliavin_setIntegral_g_eq_zero
-- name    : Malliavin.setIntegral_g_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:26:25.513443+00:00
-- url     : https://prove2.me/theorems/0ae9f7ab-188f-5bc7-9c0e-de020f3cdede
-- title:
--   Malliavin: set Integral g eq zero
-- statement:
--   All window integrals of the section-integral function of the difference vanish.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L123-L166
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L123-L166

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

theorem Malliavin.setIntegral_g_eq_zero (U : TimeProcessL2 P) {a : ℝ≥0} {A : Set W}
    (hA : MeasurableSet[𝓕 a] A) (D : TimeProcessL2 P)
    (hD : (D : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun x ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) x - U x)
    (b : ℝ≥0) {s : Set ℝ≥0} (hs : MeasurableSet s) :
    ∫ t in s, (∫ ω in A, (D : ℝ≥0 × W → ℝ) (t, ω) ∂P)
      ∂(nonnegativeLebesgueMeasure.restrict (Set.Ioc a b)) = 0 := by sorry
