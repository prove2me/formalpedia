-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianHomogeneousChaos_eq_symmetricMultipleIntegralRange_closure
-- name    : Malliavin.BrownianIteratedConstruction.brownianHomogeneousChaos_eq_symmetricMultipleIntegralRange_closure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:23:58.335134+00:00
-- url     : https://prove2.me/theorems/72f83324-1411-4268-971e-e798f9a7227d
-- title:
--   Brownian Iterated Construction: brownian Homogeneous Chaos eq symmetric Multiple Integral Range closure
-- statement:
--   The canonical Brownian homogeneous chaos is also the closure of the genuine symmetrized
--   multiple-integral range.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegral.lean#L161-L168
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegral.lean#L161-L168

import Definitions.Def_Malliavin_BrownianChaosHilbertSum
import Definitions.Def_Malliavin_BrownianMultipleIntegral
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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.BrownianIteratedConstruction.brownianHomogeneousChaos_eq_symmetricMultipleIntegralRange_closure
    (hB : IsPreBrownianReal B P) (n : ℕ) :
    (brownianHomogeneousChaos hB n : Submodule ℝ (RandomL2 P)) =
      (brownianSymmetricMultipleIntegralRange hB n).topologicalClosure := by sorry
