-- Prove2me | Theorems.Thm_Malliavin_aestronglyMeasurable_predictableDerivative
-- name    : Malliavin.aestronglyMeasurable_predictableDerivative
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:31:07.440728+00:00
-- url     : https://prove2.me/theorems/f8ab0133-8a16-4919-82cf-bc3733bf47d4
-- title:
--   Malliavin: aestrongly Measurable predictable Derivative
-- statement:
--   The Clark--Ocone integrand has a representative measurable for the predictable sigma-algebra.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L764-L770
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L764-L770

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Probability.Process.Predictable
import Definitions.Def_Malliavin_ClarkOcone
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

theorem Malliavin.aestronglyMeasurable_predictableDerivative
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) :
    AEStronglyMeasurable[𝓕.predictable]
      (predictableDerivative C F : (ℝ≥0 × W) → ℝ)
      (nonnegativeLebesgueMeasure.prod P) := by sorry
