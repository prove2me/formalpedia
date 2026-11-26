-- Prove2me | Theorems.Thm_Malliavin_hasGaussianLaw_naturalItoIntegral_deterministic
-- name    : Malliavin.hasGaussianLaw_naturalItoIntegral_deterministic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:52:22.753317+00:00
-- url     : https://prove2.me/theorems/c117ebf8-7441-5df8-8a96-d3b07f1e5dcd
-- title:
--   Malliavin: has Gaussian Law natural Ito Integral deterministic
-- statement:
--   The constructed integral of every deterministic integrand has a Gaussian law.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L211-L220
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L211-L220

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

theorem Malliavin.hasGaussianLaw_naturalItoIntegral_deterministic
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    HasGaussianLaw
      (naturalItoIntegral hB hsm hnat
        (deterministicPredictableEmbedding 𝓅 f) : W → ℝ) P := by sorry
