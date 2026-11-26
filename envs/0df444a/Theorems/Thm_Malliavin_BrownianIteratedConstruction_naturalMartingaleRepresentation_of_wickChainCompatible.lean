-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_naturalMartingaleRepresentation_of_wickChainCompatible
-- name    : Malliavin.BrownianIteratedConstruction.naturalMartingaleRepresentation_of_wickChainCompatible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:18:02.997643+00:00
-- url     : https://prove2.me/theorems/74a918d3-0b13-4472-9430-d1ceb9b7600c
-- title:
--   Brownian Iterated Construction: natural Martingale Representation of wick Chain Compatible
-- statement:
--   The exact stochastic Hermite compatibility input supplies natural martingale
--   representation.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPolynomialHermite.lean#L217-L224
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPolynomialHermite.lean#L217-L224

import Definitions.Def_Malliavin_BrownianHermite
import Definitions.Def_Malliavin_BrownianCylinderDensity
import Definitions.Def_Malliavin_BrownianChaosTotality
import Definitions.Def_Malliavin_BrownianPolynomialHermite
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.BrownianIteratedConstruction.naturalMartingaleRepresentation_of_wickChainCompatible
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hgen : IsWienerGenerated B) (hwick : BrownianWickChainCompatible hB) :
    NaturalMartingaleRepresentation hB hsm hnat := by sorry
