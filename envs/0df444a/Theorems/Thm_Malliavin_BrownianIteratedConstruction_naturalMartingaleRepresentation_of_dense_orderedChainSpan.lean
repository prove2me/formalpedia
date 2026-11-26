-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_naturalMartingaleRepresentation_of_dense_orderedChainSpan
-- name    : Malliavin.BrownianIteratedConstruction.naturalMartingaleRepresentation_of_dense_orderedChainSpan
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:59:01.790726+00:00
-- url     : https://prove2.me/theorems/eed116e2-bf96-5865-b716-4065f7dd4a34
-- title:
--   Brownian Iterated Construction: natural Martingale Representation of dense ordered Chain Span
-- statement:
--   Density of explicit ordered Brownian increment products supplies natural martingale
--   representation.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaosTotality.lean#L155-L162
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaosTotality.lean#L155-L162

import Definitions.Def_Malliavin_BrownianChaosMartingaleRepresentation
import Definitions.Def_Malliavin_BrownianChaosTotality
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

theorem Malliavin.BrownianIteratedConstruction.naturalMartingaleRepresentation_of_dense_orderedChainSpan
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hdense : Dense (brownianOrderedChainSpan hB : Set (RandomL2 P))) :
    NaturalMartingaleRepresentation hB hsm hnat := by sorry
