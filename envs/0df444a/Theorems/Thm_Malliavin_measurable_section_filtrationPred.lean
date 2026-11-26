-- Prove2me | Theorems.Thm_Malliavin_measurable_section_filtrationPred
-- name    : Malliavin.measurable_section_filtrationPred
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:27:25.400797+00:00
-- url     : https://prove2.me/theorems/5d551328-4bbb-54df-9e4a-0a23096ad72e
-- title:
--   Malliavin: measurable section filtration Pred
-- statement:
--   For `t > 0`, the map `ω ↦ (t, ω)` is measurable from the strict past `𝓕_{t⁻}` to the
--   predictable σ-algebra.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L658-L685
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L658-L685

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
  [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.measurable_section_filtrationPred {t : ℝ≥0} (ht : 0 < t) :
    @Measurable W (ℝ≥0 × W) (filtrationPred 𝓕 t) 𝓕.predictable (fun ω ↦ (t, ω)) := by sorry
