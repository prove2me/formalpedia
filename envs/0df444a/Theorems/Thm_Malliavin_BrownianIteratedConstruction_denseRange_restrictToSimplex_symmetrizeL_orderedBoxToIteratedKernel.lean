-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_denseRange_restrictToSimplex_symmetrizeL_orderedBoxToIteratedKernel
-- name    : Malliavin.BrownianIteratedConstruction.denseRange_restrictToSimplex_symmetrizeL_orderedBoxToIteratedKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:32:12.596595+00:00
-- url     : https://prove2.me/theorems/84aabce0-97ef-55bf-b2ea-0bc081cddfc3
-- title:
--   Brownian Iterated Construction: dense Range restrict To Simplex symmetrize L ordered Box To Iterated Kernel
-- statement:
--   Whenever ordered boxes are dense in simplex `L²`, symmetrized finite full-product box
--   combinations still have dense restricted range.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegralBoxSpan.lean#L64-L90
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegralBoxSpan.lean#L64-L90

import Definitions.Def_Malliavin_BrownianMultipleIntegralBox
import Definitions.Def_Malliavin_BrownianMultipleIntegralBoxSpan
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
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

theorem Malliavin.BrownianIteratedConstruction.denseRange_restrictToSimplex_symmetrizeL_orderedBoxToIteratedKernel
    (n : ℕ) (hdense : OrderedBoxDense n) :
    DenseRange fun c : OrderedBoxIndex n →₀ ℝ ↦
      restrictToSimplex n
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2
          (orderedBoxToIteratedKernel n c)) := by sorry
