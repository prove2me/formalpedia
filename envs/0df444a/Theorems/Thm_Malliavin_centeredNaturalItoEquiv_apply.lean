-- Prove2me | Theorems.Thm_Malliavin_centeredNaturalItoEquiv_apply
-- name    : Malliavin.centeredNaturalItoEquiv_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:47:52.968085+00:00
-- url     : https://prove2.me/theorems/28ac8fb3-72fc-45b0-b210-37972cf8148e
-- title:
--   Malliavin: centered Natural Ito Equiv apply
-- statement:
--   The Malliavin construction uses the centered Natural Ito Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L331-L340
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L331-L340

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

theorem Malliavin.centeredNaturalItoEquiv_apply
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hMRT : NaturalMartingaleRepresentation hB hsm hnat)
    (U : PredictableProcessL2 𝓅 P) :
    ((centeredNaturalItoEquiv hB hsm hnat hMRT U :
      (CameronMartin.expectationMap P).ker) : RandomL2 P) =
      naturalItoIntegral hB hsm hnat U := by sorry

attribute [defeq] Malliavin.centeredNaturalItoEquiv_apply
