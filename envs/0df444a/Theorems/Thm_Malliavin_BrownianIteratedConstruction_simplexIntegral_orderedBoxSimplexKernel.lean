-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_simplexIntegral_orderedBoxSimplexKernel
-- name    : Malliavin.BrownianIteratedConstruction.simplexIntegral_orderedBoxSimplexKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:49:26.808638+00:00
-- url     : https://prove2.me/theorems/ee7c7e01-916b-51e0-af25-c66ec3ea8c0a
-- title:
--   Brownian Iterated Construction: simplex Integral ordered Box Simplex Kernel
-- statement:
--   In particular, the completed map sends an ordered-box indicator to its chain product.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianIterated.lean#L507-L514
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianIterated.lean#L507-L514

import Definitions.Def_Malliavin_ItoConstruction
import Definitions.Def_Malliavin_BrownianIterated
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
open Malliavin.BrownianIteratedConstruction
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.BrownianIteratedConstruction.simplexIntegral_orderedBoxSimplexKernel
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {n : ℕ} (hdense : OrderedBoxDense n) (a : OrderedBoxIndex n) :
    simplexIntegral hB n (orderedBoxSimplexKernel a) =
      chainIntegralLp hB a.u a.v := by sorry
