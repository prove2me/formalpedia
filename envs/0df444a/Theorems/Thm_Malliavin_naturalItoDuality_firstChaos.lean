-- Prove2me | Theorems.Thm_Malliavin_naturalItoDuality_firstChaos
-- name    : Malliavin.naturalItoDuality_firstChaos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:42:12.118787+00:00
-- url     : https://prove2.me/theorems/9e6325b7-25a8-4501-a0bf-9dd2f759e910
-- title:
--   Malliavin: natural Ito Duality first Chaos
-- statement:
--   Malliavin--Itô duality for an arbitrary first-chaos terminal variable against every
--   predictable integrand.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoDuality.lean#L177-L193
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoDuality.lean#L177-L193

import Definitions.Def_Malliavin_NaturalItoRange
import Definitions.Def_Malliavin_ClarkOconeExamples
import Definitions.Def_Malliavin_NaturalItoDuality
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

theorem Malliavin.naturalItoDuality_firstChaos
    (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (Z : firstChaos hB) (U : PredictableProcessL2 𝓅 P) :
    inner ℝ ((Z : RandomL2 P) - expectationL2 (Z : RandomL2 P))
        (naturalItoIntegral hB hsm hnat U) =
      inner ℝ (predictableProjection 𝓅
        (timeDerivative hB L hL hgen
          (mderivClosure P (Z : RandomL2 P)))) U := by sorry
