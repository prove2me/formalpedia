-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianHomogeneousChaos_isOrtho
-- name    : Malliavin.BrownianIteratedConstruction.brownianHomogeneousChaos_isOrtho
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:50:26.51211+00:00
-- url     : https://prove2.me/theorems/23c9d2a4-311e-4b29-a04c-677d9bf6e550
-- title:
--   Brownian Iterated Construction: brownian Homogeneous Chaos is Ortho
-- statement:
--   Distinct closed Brownian homogeneous chaoses remain orthogonal.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaos.lean#L112-L122
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaos.lean#L112-L122

import Definitions.Def_Malliavin_BrownianOrderedBoxDensity
import Definitions.Def_Malliavin_NaturalClarkOcone
import Definitions.Def_Malliavin_NaturalItoRange
import Definitions.Def_Malliavin_BrownianChaos
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

theorem Malliavin.BrownianIteratedConstruction.brownianHomogeneousChaos_isOrtho
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {m n : ℕ} (hmn : m ≠ n) :
    (brownianHomogeneousChaos hB m : Submodule ℝ (RandomL2 P)) ⟂
      (brownianHomogeneousChaos hB n : Submodule ℝ (RandomL2 P)) := by sorry
