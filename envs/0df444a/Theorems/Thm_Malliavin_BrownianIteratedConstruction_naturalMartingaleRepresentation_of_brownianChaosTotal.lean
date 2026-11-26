-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_naturalMartingaleRepresentation_of_brownianChaosTotal
-- name    : Malliavin.BrownianIteratedConstruction.naturalMartingaleRepresentation_of_brownianChaosTotal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:57:27.95479+00:00
-- url     : https://prove2.me/theorems/ca66a57b-11b6-547c-82c8-639f28662107
-- title:
--   Brownian Iterated Construction: natural Martingale Representation of brownian Chaos Total
-- statement:
--   Totality of the canonical Brownian chaos tower supplies natural martingale
--   representation.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaosMartingaleRepresentation.lean#L38-L50
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaosMartingaleRepresentation.lean#L38-L50

import Definitions.Def_Malliavin_BrownianChaos
import Definitions.Def_Malliavin_ChaosMartingaleRepresentation
import Definitions.Def_Malliavin_BrownianChaosMartingaleRepresentation
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

theorem Malliavin.BrownianIteratedConstruction.naturalMartingaleRepresentation_of_brownianChaosTotal
    (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (htotal : BrownianChaosTotal hB) :
    NaturalMartingaleRepresentation hB hsm hnat := by sorry
