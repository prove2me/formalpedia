-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_family_isBrownian
-- name    : Malliavin.BrownianIteratedConstruction.family_isBrownian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:50:27.595871+00:00
-- url     : https://prove2.me/theorems/5337f6a8-70c1-551e-9964-ae30397255e9
-- title:
--   Brownian Iterated Construction: family is Brownian
-- statement:
--   The completed family satisfies the Brownian ordered-box compatibility at every order.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianIterated.lean#L839-L851
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianIterated.lean#L839-L851

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

theorem Malliavin.BrownianIteratedConstruction.family_isBrownian
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    (hdense : PositiveOrderedBoxDense) :
    (family hB hsm hdense).IsBrownian B := by sorry
