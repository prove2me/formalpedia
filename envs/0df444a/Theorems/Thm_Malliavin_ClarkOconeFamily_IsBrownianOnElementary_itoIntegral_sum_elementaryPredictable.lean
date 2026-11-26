-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_IsBrownianOnElementary_itoIntegral_sum_elementaryPredictable
-- name    : Malliavin.ClarkOconeFamily.IsBrownianOnElementary.itoIntegral_sum_elementaryPredictable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:30:38.573791+00:00
-- url     : https://prove2.me/theorems/67dea14b-cfa3-4fce-afa6-2a68be12afbb
-- title:
--   Is Brownian On Elementary: ito Integral sum elementary Predictable
-- statement:
--   Brownian compatibility on one-step adapted integrands extends by linearity to finite sums.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L655-L665
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L655-L665

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

theorem Malliavin.ClarkOconeFamily.IsBrownianOnElementary.itoIntegral_sum_elementaryPredictable
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} {C : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnElementary) {ι : Type*} (s : Finset ι)
    (a b : ι → ℝ≥0) (hab : ∀ i, a i ≤ b i)
    (Z : ∀ i, lpMeas ℝ ℝ (𝓕 (a i)) 2 P) :
    C.itoIntegral (s.sum fun i ↦ elementaryPredictable 𝓕 (a i) (b i) (Z i)) =
      s.sum fun i ↦ C.elementaryIntegralValue (hab i) (Z i) := by sorry
