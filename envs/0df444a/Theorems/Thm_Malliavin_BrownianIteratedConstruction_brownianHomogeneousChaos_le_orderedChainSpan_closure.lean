-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianHomogeneousChaos_le_orderedChainSpan_closure
-- name    : Malliavin.BrownianIteratedConstruction.brownianHomogeneousChaos_le_orderedChainSpan_closure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:00:21.558157+00:00
-- url     : https://prove2.me/theorems/f218e727-ced7-4a42-b9ba-bcd0af0281fd
-- title:
--   Brownian Iterated Construction: brownian Homogeneous Chaos le ordered Chain Span closure
-- statement:
--   Each completed Brownian homogeneous chaos lies in the closed span of explicit ordered
--   increment products.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaosTotality.lean#L115-L123
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaosTotality.lean#L115-L123

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

theorem Malliavin.BrownianIteratedConstruction.brownianHomogeneousChaos_le_orderedChainSpan_closure
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) (n : ℕ) :
    (brownianHomogeneousChaos hB n : Submodule ℝ (RandomL2 P)) ≤
      (brownianOrderedChainSpan hB).topologicalClosure := by sorry
