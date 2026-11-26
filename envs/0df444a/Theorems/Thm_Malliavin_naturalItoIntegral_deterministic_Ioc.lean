-- Prove2me | Theorems.Thm_Malliavin_naturalItoIntegral_deterministic_Ioc
-- name    : Malliavin.naturalItoIntegral_deterministic_Ioc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:52:14.222182+00:00
-- url     : https://prove2.me/theorems/08dd7632-f30d-5b88-9bea-6f1ea4c7a28d
-- title:
--   Malliavin: natural Ito Integral deterministic Ioc
-- statement:
--   On the deterministic indicator of `(a,b]`, the constructed Itô integral is the Brownian
--   increment `B_b - B_a` in `L²(P)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L174-L184
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L174-L184

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

theorem Malliavin.naturalItoIntegral_deterministic_Ioc
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) :
    naturalItoIntegral hB hsm hnat (deterministicPredictableEmbedding 𝓅
      (indicatorConstLp 2 measurableSet_Ioc
        (nonnegativeLebesgueMeasure_Ioc_ne_top a b) (1 : ℝ))) =
      brownianLp hB b - brownianLp hB a := by sorry
