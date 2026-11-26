-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_restrictToSimplex_symmetrizeL_boxKernel
-- name    : Malliavin.BrownianIteratedConstruction.restrictToSimplex_symmetrizeL_boxKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:12:53.868299+00:00
-- url     : https://prove2.me/theorems/452a67d2-a948-423f-a639-fa9e0a51e11d
-- title:
--   Brownian Iterated Construction: restrict To Simplex symmetrize L box Kernel
-- statement:
--   Restricting a symmetrized ordered-box indicator to the strict simplex leaves exactly its
--   identity-permutation contribution.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegralBox.lean#L33-L79
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegralBox.lean#L33-L79

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Definitions.Def_Malliavin_BrownianMultipleIntegralBox
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.BrownianIteratedConstruction.restrictToSimplex_symmetrizeL_boxKernel {n : ℕ} (a : OrderedBoxIndex n) :
    restrictToSimplex n
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 (boxKernel a.u a.v)) =
      ((n.factorial : ℝ)⁻¹) • orderedBoxSimplexKernel a := by sorry
