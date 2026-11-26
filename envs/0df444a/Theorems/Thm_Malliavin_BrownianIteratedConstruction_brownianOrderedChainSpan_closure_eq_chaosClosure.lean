-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianOrderedChainSpan_closure_eq_chaosClosure
-- name    : Malliavin.BrownianIteratedConstruction.brownianOrderedChainSpan_closure_eq_chaosClosure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:58:48.795792+00:00
-- url     : https://prove2.me/theorems/c910dd75-d29d-58cf-a12f-7663d06a6c1f
-- title:
--   Brownian Iterated Construction: brownian Ordered Chain Span closure eq chaos Closure
-- statement:
--   Completing the explicit ordered increment products gives exactly the closed span of the
--   canonical Brownian homogeneous chaoses.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaosTotality.lean#L128-L141
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaosTotality.lean#L128-L141

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

theorem Malliavin.BrownianIteratedConstruction.brownianOrderedChainSpan_closure_eq_chaosClosure
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    (brownianOrderedChainSpan hB).topologicalClosure =
      (⨆ n : ℕ, (brownianHomogeneousChaos hB n : Submodule ℝ (RandomL2 P))
        ).topologicalClosure := by sorry
