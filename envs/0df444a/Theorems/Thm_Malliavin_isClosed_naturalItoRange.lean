-- Prove2me | Theorems.Thm_Malliavin_isClosed_naturalItoRange
-- name    : Malliavin.isClosed_naturalItoRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:49:17.872895+00:00
-- url     : https://prove2.me/theorems/a7a33534-23ca-4fd2-8975-e80667d6a840
-- title:
--   Malliavin: is Closed natural Ito Range
-- statement:
--   The natural Itô terminal-value subspace is closed in `L²(P)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L41-L46
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L41-L46

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

theorem Malliavin.isClosed_naturalItoRange
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    IsClosed (naturalItoRange hB hsm hnat : Set (RandomL2 P)) := by sorry
