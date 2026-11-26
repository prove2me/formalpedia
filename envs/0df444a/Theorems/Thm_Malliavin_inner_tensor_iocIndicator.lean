-- Prove2me | Theorems.Thm_Malliavin_inner_tensor_iocIndicator
-- name    : Malliavin.inner_tensor_iocIndicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:28:09.827429+00:00
-- url     : https://prove2.me/theorems/f15b7711-09d9-4ebc-8d32-be9eafdcf359
-- title:
--   Malliavin: inner tensor ioc Indicator
-- statement:
--   Pairing a product-`L²` process with the elementary tensor `1_{(c,d]} ⊗ g` computes the
--   window integral of the sectionwise pairings.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L373-L418
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L373-L418

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

theorem Malliavin.inner_tensor_iocIndicator (D : TimeProcessL2 P) (c d : ℝ≥0) (g : Lp ℝ 2 P) :
    ⟪D, tensor (iocIndicator c d) g⟫_ℝ =
      ∫ t in Set.Ioc c d, (∫ ω, D (t, ω) * g ω ∂P) ∂nonnegativeLebesgueMeasure := by sorry
