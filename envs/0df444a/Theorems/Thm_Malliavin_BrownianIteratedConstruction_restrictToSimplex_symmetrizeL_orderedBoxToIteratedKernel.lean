-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_restrictToSimplex_symmetrizeL_orderedBoxToIteratedKernel
-- name    : Malliavin.BrownianIteratedConstruction.restrictToSimplex_symmetrizeL_orderedBoxToIteratedKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:20:48.38547+00:00
-- url     : https://prove2.me/theorems/08f9779e-e76a-5a47-8db7-a73526e86bcf
-- title:
--   Brownian Iterated Construction: restrict To Simplex symmetrize L ordered Box To Iterated Kernel
-- statement:
--   Restriction after symmetrization sends a finite full-product box combination to the
--   corresponding simplex combination with the inverse-factorial normalization.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegralBoxSpan.lean#L47-L58
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegralBoxSpan.lean#L47-L58

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

theorem Malliavin.BrownianIteratedConstruction.restrictToSimplex_symmetrizeL_orderedBoxToIteratedKernel
    (n : ℕ) (c : OrderedBoxIndex n →₀ ℝ) :
    restrictToSimplex n
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2
          (orderedBoxToIteratedKernel n c)) =
      ((n.factorial : ℝ)⁻¹) • orderedBoxToSimplexKernel n c := by sorry
