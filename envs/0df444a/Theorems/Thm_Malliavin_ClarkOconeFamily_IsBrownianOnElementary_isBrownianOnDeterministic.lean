-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_IsBrownianOnElementary_isBrownianOnDeterministic
-- name    : Malliavin.ClarkOconeFamily.IsBrownianOnElementary.isBrownianOnDeterministic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:30:29.578107+00:00
-- url     : https://prove2.me/theorems/92d951bd-a0dc-59b9-bb66-f331eea92074
-- title:
--   Is Brownian On Elementary: is Brownian On Deterministic
-- statement:
--   Brownian compatibility on adapted elementary processes entails compatibility on every
--   deterministic interval indicator.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L690-L697
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L690-L697

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

theorem Malliavin.ClarkOconeFamily.IsBrownianOnElementary.isBrownianOnDeterministic
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} {C : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnElementary) : C.IsBrownianOnDeterministic := by sorry
