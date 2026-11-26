-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_hasSum_brownianPositiveTowerLI
-- name    : Malliavin.BrownianIteratedConstruction.hasSum_brownianPositiveTowerLI
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:23:02.272379+00:00
-- url     : https://prove2.me/theorems/7bd3fe79-4172-41bc-a26d-69fb61759d35
-- title:
--   Brownian Iterated Construction: has Sum brownian Positive Tower LI
-- statement:
--   The global positive-tower value is the convergent sum of its canonical orderwise simplex
--   integrals.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaosHilbertSum.lean#L81-L87
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaosHilbertSum.lean#L81-L87

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

theorem Malliavin.BrownianIteratedConstruction.hasSum_brownianPositiveTowerLI
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (f : IteratedIntegralConstruction.PositiveKernelSum) :
    HasSum (fun n => simplexIntegral hB (n + 1) (f n))
      (brownianPositiveTowerLI hB hsm f) := by sorry
