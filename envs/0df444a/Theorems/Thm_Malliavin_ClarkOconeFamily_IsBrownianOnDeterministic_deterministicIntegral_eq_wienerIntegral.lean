-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_IsBrownianOnDeterministic_deterministicIntegral_eq_wienerIntegral
-- name    : Malliavin.ClarkOconeFamily.IsBrownianOnDeterministic.deterministicIntegral_eq_wienerIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:15:10.577987+00:00
-- url     : https://prove2.me/theorems/c3d36b21-2721-458c-a0b4-5ec1900b9f08
-- title:
--   Is Brownian On Deterministic: deterministic Integral eq wiener Integral
-- statement:
--   Agreement on the interval indicators determines the designated integral on every
--   deterministic square-integrable integrand.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L713-L721
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L713-L721

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Probability.Process.Predictable
import Definitions.Def_Malliavin_ClarkOcone
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

theorem Malliavin.ClarkOconeFamily.IsBrownianOnDeterministic.deterministicIntegral_eq_wienerIntegral
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} {C : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnDeterministic) :
    C.deterministicIntegral = wienerIntegral C.isPreBrownian := by sorry
