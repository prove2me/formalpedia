-- Prove2me | Theorems.Thm_Malliavin_iocIndicator_eq_intervalIndicator_sub
-- name    : Malliavin.iocIndicator_eq_intervalIndicator_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:46:33.909863+00:00
-- url     : https://prove2.me/theorems/7349c8fa-39a8-4746-b2f8-babfa0163d4e
-- title:
--   Malliavin: ioc Indicator eq interval Indicator sub
-- statement:
--   The interval kernel used for elementary predictable processes is the difference of the two
--   initial-interval kernels.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalClarkOcone.lean#L32-L39
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalClarkOcone.lean#L32-L39

import Definitions.Def_Malliavin_KernelIdentification
import Definitions.Def_Malliavin_NaturalClarkOcone
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.iocIndicator_eq_intervalIndicator_sub
    (hB : IsPreBrownianReal B P) {a b : ℝ≥0} (hab : a ≤ b) :
    iocIndicator a b = intervalIndicator b - intervalIndicator a := by sorry
