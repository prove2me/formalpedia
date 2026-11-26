-- Prove2me | Theorems.Thm_Malliavin_inner_naturalItoIntegral_wienerIntegral
-- name    : Malliavin.inner_naturalItoIntegral_wienerIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:48:03.969961+00:00
-- url     : https://prove2.me/theorems/9b2182da-db28-4ad5-8822-779daa896389
-- title:
--   Malliavin: inner natural Ito Integral wiener Integral
-- statement:
--   The covariance with a deterministic Wiener integral is the predictable-space inner product
--   against the deterministic embedding.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L239-L248
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L239-L248

import Definitions.Def_Malliavin_ItoConstruction
import Definitions.Def_Malliavin_ItoConsequences
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

theorem Malliavin.inner_naturalItoIntegral_wienerIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (U : PredictableProcessL2 𝓅 P)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    inner ℝ (naturalItoIntegral hB hsm hnat U) (wienerIntegral hB f) =
      inner ℝ U (deterministicPredictableEmbedding 𝓅 f) := by sorry
