-- Prove2me | Theorems.Thm_Malliavin_map_naturalItoIntegral_deterministic_eq_gaussianReal
-- name    : Malliavin.map_naturalItoIntegral_deterministic_eq_gaussianReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:54:00.631015+00:00
-- url     : https://prove2.me/theorems/e1d43291-2357-42f0-8855-3349bfe988cd
-- title:
--   Malliavin: map natural Ito Integral deterministic eq gaussian Real
-- statement:
--   The law is the centered Gaussian whose variance is the deterministic integrand's squared
--   `L²` norm.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L225-L234
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L225-L234

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

theorem Malliavin.map_naturalItoIntegral_deterministic_eq_gaussianReal
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    P.map (naturalItoIntegral hB hsm hnat
      (deterministicPredictableEmbedding 𝓅 f)) =
        gaussianReal 0 (‖f‖₊ ^ 2) := by sorry
