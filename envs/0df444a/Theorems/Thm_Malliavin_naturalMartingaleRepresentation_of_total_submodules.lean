-- Prove2me | Theorems.Thm_Malliavin_naturalMartingaleRepresentation_of_total_submodules
-- name    : Malliavin.naturalMartingaleRepresentation_of_total_submodules
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:53:47.65335+00:00
-- url     : https://prove2.me/theorems/07ee9882-b4ef-5d3d-b628-96d6c43b84bb
-- title:
--   Malliavin: natural Martingale Representation of total submodules
-- statement:
--   Any total graded family whose zeroth component is killed by centering and whose positive
--   components lie in the natural Itô range supplies martingale representation.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChaosMartingaleRepresentation.lean#L32-L79
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChaosMartingaleRepresentation.lean#L32-L79

import Definitions.Def_Malliavin_NaturalClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Definitions.Def_Malliavin_ChaosMartingaleRepresentation
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

theorem Malliavin.naturalMartingaleRepresentation_of_total_submodules
    (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (K : ℕ → Submodule ℝ (RandomL2 P))
    (htotal : (⨆ n : ℕ, K n).topologicalClosure = ⊤)
    (hzero : K 0 ≤ (centeredPartCLM (P := P)).ker)
    (hpositive : ∀ n : ℕ, 0 < n → K n ≤ naturalItoRange hB hsm hnat) :
    NaturalMartingaleRepresentation hB hsm hnat := by sorry
