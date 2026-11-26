-- Prove2me | Theorems.Thm_Malliavin_naturalMartingaleRepresentation_iff_range_eq_expectationMap_ker
-- name    : Malliavin.naturalMartingaleRepresentation_iff_range_eq_expectationMap_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:52:58.023917+00:00
-- url     : https://prove2.me/theorems/a838f255-684b-5d10-95cc-0da98081f73f
-- title:
--   Malliavin: natural Martingale Representation iff range eq expectation Map ker
-- statement:
--   Equivalently, martingale representation says that the constructed Itô range is the entire
--   closed subspace of centered random variables.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L371-L393
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L371-L393

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

theorem Malliavin.naturalMartingaleRepresentation_iff_range_eq_expectationMap_ker
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    NaturalMartingaleRepresentation hB hsm hnat ↔
      LinearMap.range (naturalItoIntegral hB hsm hnat).toLinearMap =
        (CameronMartin.expectationMap P).ker := by sorry
