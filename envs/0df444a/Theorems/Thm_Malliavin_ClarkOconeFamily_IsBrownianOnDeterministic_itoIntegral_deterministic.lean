-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_IsBrownianOnDeterministic_itoIntegral_deterministic
-- name    : Malliavin.ClarkOconeFamily.IsBrownianOnDeterministic.itoIntegral_deterministic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:20:57.143398+00:00
-- url     : https://prove2.me/theorems/d762a846-d914-52a9-add9-999e8f7bef2f
-- title:
--   Is Brownian On Deterministic: ito Integral deterministic
-- statement:
--   The designated integral agrees with the genuine Wiener integral on every deterministic
--   integrand.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L738-L743
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L738-L743

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

theorem Malliavin.ClarkOconeFamily.IsBrownianOnDeterministic.itoIntegral_deterministic
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} {C : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnDeterministic) (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    C.itoIntegral (deterministicPredictableEmbedding 𝓕 f) =
      wienerIntegral C.isPreBrownian f := by sorry
