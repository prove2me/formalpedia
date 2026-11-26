-- Prove2me | Theorems.Thm_Malliavin_naturalMartingaleRepresentation_iff_centeredNaturalItoRange_orthogonal_eq_bot
-- name    : Malliavin.naturalMartingaleRepresentation_iff_centeredNaturalItoRange_orthogonal_eq_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:51:45.488397+00:00
-- url     : https://prove2.me/theorems/dd094186-f6da-51df-90d1-78e8e3014f82
-- title:
--   Malliavin: natural Martingale Representation iff centered Natural Ito Range orthogonal eq bot
-- statement:
--   Martingale representation holds exactly when no nonzero centered random variable is
--   orthogonal to every natural Itô terminal value.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L344-L353
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L344-L353

import Definitions.Def_Malliavin_ItoConsequences
import Definitions.Def_Malliavin_NaturalItoRange
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

theorem Malliavin.naturalMartingaleRepresentation_iff_centeredNaturalItoRange_orthogonal_eq_bot
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    NaturalMartingaleRepresentation hB hsm hnat ↔
      (centeredNaturalItoRange hB hsm hnat)ᗮ = ⊥ := by sorry
