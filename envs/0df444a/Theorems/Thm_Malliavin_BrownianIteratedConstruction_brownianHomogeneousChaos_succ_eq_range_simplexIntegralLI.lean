-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianHomogeneousChaos_succ_eq_range_simplexIntegralLI
-- name    : Malliavin.BrownianIteratedConstruction.brownianHomogeneousChaos_succ_eq_range_simplexIntegralLI
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:01:45.987097+00:00
-- url     : https://prove2.me/theorems/9f7f0da5-fc96-5f87-a326-0b6eb31b1543
-- title:
--   Brownian Iterated Construction: brownian Homogeneous Chaos succ eq range simplex Integral LI
-- statement:
--   The completed canonical chaos of positive order `n + 1` is precisely the closed range of
--   the corresponding simplex isometry.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaosHilbertSum.lean#L92-L116
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaosHilbertSum.lean#L92-L116

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

theorem Malliavin.BrownianIteratedConstruction.brownianHomogeneousChaos_succ_eq_range_simplexIntegralLI
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) (n : ℕ) :
    (brownianHomogeneousChaos hB (n + 1) : Submodule ℝ (RandomL2 P)) =
      LinearMap.range (brownianSimplexIntegralLI hB hsm n).toLinearMap := by sorry
