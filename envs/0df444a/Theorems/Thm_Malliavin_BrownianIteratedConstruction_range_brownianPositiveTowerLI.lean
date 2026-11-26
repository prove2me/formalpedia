-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_range_brownianPositiveTowerLI
-- name    : Malliavin.BrownianIteratedConstruction.range_brownianPositiveTowerLI
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:02:38.416783+00:00
-- url     : https://prove2.me/theorems/aa41d91e-978a-4317-a953-9cbcfa31d353
-- title:
--   Brownian Iterated Construction: range brownian Positive Tower LI
-- statement:
--   The range of the global positive tower is the closed supremum of the positive canonical
--   Brownian chaoses.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaosHilbertSum.lean#L121-L131
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaosHilbertSum.lean#L121-L131

import Definitions.Def_Malliavin_BrownianChaosTotality
import Definitions.Def_Malliavin_BrownianChaosHilbertSum
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

theorem Malliavin.BrownianIteratedConstruction.range_brownianPositiveTowerLI
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    LinearMap.range (brownianPositiveTowerLI hB hsm).toLinearMap =
      (⨆ n : ℕ,
        (brownianHomogeneousChaos hB (n + 1) : Submodule ℝ (RandomL2 P))
      ).topologicalClosure := by sorry
