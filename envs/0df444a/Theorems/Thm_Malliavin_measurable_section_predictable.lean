-- Prove2me | Theorems.Thm_Malliavin_measurable_section_predictable
-- name    : Malliavin.measurable_section_predictable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:26:50.950417+00:00
-- url     : https://prove2.me/theorems/260a35f3-7700-5427-b790-da94ad8cd061
-- title:
--   Malliavin: measurable section predictable
-- statement:
--   The map `ω ↦ (t, ω)` is measurable from `𝓕 t` to the predictable σ-algebra.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L249-L280
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L249-L280

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W]

theorem Malliavin.measurable_section_predictable (t : ℝ≥0) :
    @Measurable W (ℝ≥0 × W) (𝓕 t) 𝓕.predictable (fun ω ↦ (t, ω)) := by sorry
