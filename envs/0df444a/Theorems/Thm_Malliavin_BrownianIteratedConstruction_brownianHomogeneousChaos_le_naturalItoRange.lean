-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianHomogeneousChaos_le_naturalItoRange
-- name    : Malliavin.BrownianIteratedConstruction.brownianHomogeneousChaos_le_naturalItoRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:47:44.433913+00:00
-- url     : https://prove2.me/theorems/8edc1124-93cd-4dcf-879b-7e32e48c699b
-- title:
--   Brownian Iterated Construction: brownian Homogeneous Chaos le natural Ito Range
-- statement:
--   Every positive Brownian homogeneous chaos lies in the natural Itô range.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaos.lean#L149-L161
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaos.lean#L149-L161

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

theorem Malliavin.BrownianIteratedConstruction.brownianHomogeneousChaos_le_naturalItoRange
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) (n : ℕ) (hn : 0 < n) :
    (brownianHomogeneousChaos hB n : Submodule ℝ (RandomL2 P)) ≤
      naturalItoRange hB hsm hnat := by sorry
