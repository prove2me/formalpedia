-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_IsBrownianOnDeterministic_duality_wienerIntegral
-- name    : Malliavin.ClarkOconeFamily.IsBrownianOnDeterministic.duality_wienerIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:38:01.250874+00:00
-- url     : https://prove2.me/theorems/117102b1-2b87-41f7-9b0f-57020606b91a
-- title:
--   Is Brownian On Deterministic: duality wiener Integral
-- statement:
--   **The Malliavin--Itô duality holds on the first chaos against deterministic integrands** for
--   every family whose integral is Brownian on deterministic integrands: for `F = ∫ g dB` and
--   `u = h ⊗ 1`, `⟪F - E F, itoIntegral u⟫ = ⟪predictableProjection (Dₜ F), u⟫ = ⟪g, h⟫`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L78-L101
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L78-L101

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_CylindricalGrowth
import Definitions.Def_Malliavin_ChainRule
import Definitions.Def_Malliavin_ClarkOconeExamples
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}

theorem Malliavin.ClarkOconeFamily.IsBrownianOnDeterministic.duality_wienerIntegral
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} {C : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnDeterministic) (g h : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ⟪wienerIntegral C.isPreBrownian g - expectationL2 (wienerIntegral C.isPreBrownian g),
        C.itoIntegral (deterministicPredictableEmbedding 𝓕 h)⟫_ℝ =
      ⟪predictableProjection 𝓕
        (C.timeDerivative (mderivClosure P (wienerIntegral C.isPreBrownian g))),
        deterministicPredictableEmbedding 𝓕 h⟫_ℝ := by sorry
