-- Prove2me | Theorems.Thm_Malliavin_isClosed_range_naturalItoIntegral
-- name    : Malliavin.isClosed_range_naturalItoIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:51:51.020736+00:00
-- url     : https://prove2.me/theorems/55cedfa9-b1bb-4b59-a450-adb73ce02275
-- title:
--   Malliavin: is Closed range natural Ito Integral
-- statement:
--   The range of the constructed Itô isometry is closed.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L397-L406
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L397-L406

import Definitions.Def_Malliavin_ItoConstruction
import Definitions.Def_Malliavin_ItoConsequences
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
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.isClosed_range_naturalItoIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    IsClosed (LinearMap.range (naturalItoIntegral hB hsm hnat).toLinearMap :
      Set (RandomL2 P)) := by sorry
