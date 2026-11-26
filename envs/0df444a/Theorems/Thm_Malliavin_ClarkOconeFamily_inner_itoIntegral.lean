-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_inner_itoIntegral
-- name    : Malliavin.ClarkOconeFamily.inner_itoIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:21:14.370237+00:00
-- url     : https://prove2.me/theorems/9901961a-6346-4ec8-87f5-5aa9a29ecf6c
-- title:
--   Clark Ocone Family: inner ito Integral
-- statement:
--   The norm isometry of the designated integral polarizes to preservation of inner products.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L442-L445
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L442-L445

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

theorem Malliavin.ClarkOconeFamily.inner_itoIntegral {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (u v : PredictableProcessL2 𝓕 P) :
    inner ℝ (C.itoIntegral u) (C.itoIntegral v) = inner ℝ u v := by sorry
