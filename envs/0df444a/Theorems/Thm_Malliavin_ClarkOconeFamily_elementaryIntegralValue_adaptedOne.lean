-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_elementaryIntegralValue_adaptedOne
-- name    : Malliavin.ClarkOconeFamily.elementaryIntegralValue_adaptedOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:22:37.34241+00:00
-- url     : https://prove2.me/theorems/06063b91-b030-4399-85ee-cf02f44ecd84
-- title:
--   Clark Ocone Family: elementary Integral Value adapted One
-- statement:
--   The terminal value attached to a constant-coefficient elementary process is its Brownian
--   increment.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L571-L589
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L571-L589

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

theorem Malliavin.ClarkOconeFamily.elementaryIntegralValue_adaptedOne
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {a b : ℝ≥0} (hab : a ≤ b) :
    C.elementaryIntegralValue hab (adaptedOne (P := P) 𝓕 a) =
      brownianLp C.isPreBrownian b - brownianLp C.isPreBrownian a := by sorry
