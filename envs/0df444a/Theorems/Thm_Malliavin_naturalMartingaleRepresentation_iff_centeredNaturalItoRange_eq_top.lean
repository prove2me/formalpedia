-- Prove2me | Theorems.Thm_Malliavin_naturalMartingaleRepresentation_iff_centeredNaturalItoRange_eq_top
-- name    : Malliavin.naturalMartingaleRepresentation_iff_centeredNaturalItoRange_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:51:37.000484+00:00
-- url     : https://prove2.me/theorems/d5659324-3580-461b-84f7-0015c1f33732
-- title:
--   Malliavin: natural Martingale Representation iff centered Natural Ito Range eq top
-- statement:
--   Martingale representation is equivalent to the centered natural Itô range being the whole
--   centered `L²(P)` space.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L332-L339
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L332-L339

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

theorem Malliavin.naturalMartingaleRepresentation_iff_centeredNaturalItoRange_eq_top
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    NaturalMartingaleRepresentation hB hsm hnat ↔
      centeredNaturalItoRange hB hsm hnat = ⊤ := by sorry
