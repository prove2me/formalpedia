-- Prove2me | Theorems.Thm_Malliavin_mem_centeredNaturalItoRange_iff
-- name    : Malliavin.mem_centeredNaturalItoRange_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:54:01.388872+00:00
-- url     : https://prove2.me/theorems/5ff7c545-bd22-5b39-88db-4947aafbef41
-- title:
--   Malliavin: mem centered Natural Ito Range iff
-- statement:
--   Membership in the intrinsic centered range is equivalent to ambient membership in the
--   natural Itô range.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L95-L111
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L95-L111

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

theorem Malliavin.mem_centeredNaturalItoRange_iff
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (G : (CameronMartin.expectationMap P).ker) :
    G ∈ centeredNaturalItoRange hB hsm hnat ↔
      (G : RandomL2 P) ∈ naturalItoRange hB hsm hnat := by sorry
