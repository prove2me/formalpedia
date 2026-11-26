-- Prove2me | Theorems.Thm_Malliavin_inner_elementaryBrownianValue_eq_inner_elementaryPredictable_same
-- name    : Malliavin.inner_elementaryBrownianValue_eq_inner_elementaryPredictable_same
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:19:07.543945+00:00
-- url     : https://prove2.me/theorems/074ea259-f06a-4001-bc35-78c12ea33027
-- title:
--   Malliavin: inner elementary Brownian Value eq inner elementary Predictable same
-- statement:
--   The cross-inner-product identity for two constructed elementary Brownian values on the same
--   interval.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ElementaryIto.lean#L539-L606
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ElementaryIto.lean#L539-L606

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_ElementaryIto
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

theorem Malliavin.inner_elementaryBrownianValue_eq_inner_elementaryPredictable_same
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) (Z Y : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    inner ℝ (elementaryBrownianValue hB hsm hnat hab Z)
      (elementaryBrownianValue hB hsm hnat hab Y) =
    inner ℝ (elementaryPredictable 𝓕 a b Z)
      (elementaryPredictable 𝓕 a b Y) := by sorry
