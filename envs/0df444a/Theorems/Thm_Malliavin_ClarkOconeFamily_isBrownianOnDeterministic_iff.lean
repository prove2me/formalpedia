-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_isBrownianOnDeterministic_iff
-- name    : Malliavin.ClarkOconeFamily.isBrownianOnDeterministic_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:30:37.057948+00:00
-- url     : https://prove2.me/theorems/f80cad5d-c785-4300-bacf-2f997f6c1d77
-- title:
--   Clark Ocone Family: is Brownian On Deterministic iff
-- statement:
--   Deterministic Brownian compatibility is equivalent to equality with the genuine Wiener
--   integral on the entire deterministic `L²` subspace.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L725-L734
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L725-L734

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

theorem Malliavin.ClarkOconeFamily.isBrownianOnDeterministic_iff
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕) :
    C.IsBrownianOnDeterministic ↔
      C.deterministicIntegral = wienerIntegral C.isPreBrownian := by sorry
