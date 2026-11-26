-- Prove2me | Theorems.Thm_Malliavin_eq_predictableDerivative_of_representation
-- name    : Malliavin.eq_predictableDerivative_of_representation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:21:05.341788+00:00
-- url     : https://prove2.me/theorems/72736fb6-9904-51c9-873a-8eae92490772
-- title:
--   Malliavin: eq predictable Derivative of representation
-- statement:
--   The stipulated duality uniquely identifies any representing integrand with the predictable
--   derivative.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L795-L812
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L795-L812

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

theorem Malliavin.eq_predictableDerivative_of_representation
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) (u : PredictableProcessL2 𝓕 P)
    (hu : F.1 = expectationL2 F.1 + C.itoIntegral u) :
    u = predictableDerivative C F := by sorry
