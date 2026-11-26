-- Prove2me | Theorems.Thm_Malliavin_naturalMartingaleRepresentation_iff_bestNaturalItoIntegrand_exact
-- name    : Malliavin.naturalMartingaleRepresentation_iff_bestNaturalItoIntegrand_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:54:31.568602+00:00
-- url     : https://prove2.me/theorems/fb7a953d-19b0-580e-a5f7-bb60d49b0f90
-- title:
--   Malliavin: natural Martingale Representation iff best Natural Ito Integrand exact
-- statement:
--   Martingale representation is also equivalent to the canonical best-integrand operator being
--   an exact right inverse on every centered terminal variable.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L419-L433
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L419-L433

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

theorem Malliavin.naturalMartingaleRepresentation_iff_bestNaturalItoIntegrand_exact
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    NaturalMartingaleRepresentation hB hsm hnat ↔
      ∀ G : (CameronMartin.expectationMap P).ker,
        centeredNaturalItoIntegralIsometry hB hsm hnat
          (bestNaturalItoIntegrand hB hsm hnat G) = G := by sorry
