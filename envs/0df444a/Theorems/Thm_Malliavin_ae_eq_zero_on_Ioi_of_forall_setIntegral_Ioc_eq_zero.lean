-- Prove2me | Theorems.Thm_Malliavin_ae_eq_zero_on_Ioi_of_forall_setIntegral_Ioc_eq_zero
-- name    : Malliavin.ae_eq_zero_on_Ioi_of_forall_setIntegral_Ioc_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:27:01.066909+00:00
-- url     : https://prove2.me/theorems/b667d0b7-f16f-5589-bd8f-83a11e8171fe
-- title:
--   Malliavin: ae eq zero on Ioi of forall set Integral Ioc eq zero
-- statement:
--   A locally integrable function on `(a, ∞)` whose integrals over all intervals `(c, d]` with
--   `a ≤ c` vanish is zero almost everywhere on `(a, ∞)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L324-L368
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L324-L368

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

theorem Malliavin.ae_eq_zero_on_Ioi_of_forall_setIntegral_Ioc_eq_zero {h : ℝ≥0 → ℝ} {a : ℝ≥0}
    (hloc : ∀ b : ℝ≥0, IntegrableOn h (Set.Ioc a b) nonnegativeLebesgueMeasure)
    (hzero : ∀ c d : ℝ≥0, a ≤ c →
      ∫ t in Set.Ioc c d, h t ∂nonnegativeLebesgueMeasure = 0) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, a < t → h t = 0 := by sorry
