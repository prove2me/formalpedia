-- Prove2me | Theorems.Thm_Malliavin_inner_naturalItoIntegral_brownianLp
-- name    : Malliavin.inner_naturalItoIntegral_brownianLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:52:57.994806+00:00
-- url     : https://prove2.me/theorems/27cfc84a-8933-5730-bcfd-51581b9e61e6
-- title:
--   Malliavin: inner natural Ito Integral brownian Lp
-- statement:
--   In particular, covariance with `B_t` is the predictable inner product against
--   `1_(0,t]`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L253-L262
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L253-L262

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

theorem Malliavin.inner_naturalItoIntegral_brownianLp
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (U : PredictableProcessL2 𝓅 P) (t : ℝ≥0) :
    inner ℝ (naturalItoIntegral hB hsm hnat U) (brownianLp hB t) =
      inner ℝ U
        (deterministicPredictableEmbedding 𝓅 (intervalIndicator t)) := by sorry
