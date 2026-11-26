-- Prove2me | Theorems.Thm_Malliavin_bestNaturalItoIntegrand_centeredWienerIntegral
-- name    : Malliavin.bestNaturalItoIntegrand_centeredWienerIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:50:00.052395+00:00
-- url     : https://prove2.me/theorems/331190d4-d507-468e-b71c-3617813f2474
-- title:
--   Malliavin: best Natural Ito Integrand centered Wiener Integral
-- statement:
--   The canonical best integrand of a first-chaos Wiener integral is exactly its deterministic
--   kernel, without any martingale-representation assumption.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L251-L265
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L251-L265

import Definitions.Def_Malliavin_ItoConsequences
import Definitions.Def_Malliavin_NaturalItoRange
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
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.bestNaturalItoIntegrand_centeredWienerIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    bestNaturalItoIntegrand hB hsm hnat (centeredWienerIntegral hB g) =
      deterministicPredictableEmbedding 𝓅 g := by sorry
