-- Prove2me | Theorems.Thm_Malliavin_timeDerivative_mderivLp_cylinder
-- name    : Malliavin.timeDerivative_mderivLp_cylinder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:29:12.040853+00:00
-- url     : https://prove2.me/theorems/4456eb52-7a4f-551d-a53d-201d9eff5f36
-- title:
--   Malliavin: time Derivative mderiv Lp cylinder
-- statement:
--   **The textbook Malliavin derivative of a cylindrical functional**:
--   `Dₜ f(B t₁, …, B tₙ) = ∑ᵢ ∂ᵢ f (B t₁, …, B tₙ) · 1_{(0, tᵢ]}(t)` in `L²(ℝ≥0 × W)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L590-L601
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L590-L601

import Definitions.Def_Malliavin_WienerIntegral
import Definitions.Def_Malliavin_FubiniLift
import Definitions.Def_Malliavin_MalliavinDerivative
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_TimeDerivative
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
variable (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w)
include L hL

theorem Malliavin.timeDerivative_mderivLp_cylinder (hgen : IsWienerGenerated B) {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (hb : ∃ C, ∀ y, |f y| ≤ C)
    (hb' : ∃ C, ∀ y, ‖fderiv ℝ f y‖ ≤ C) (t : Fin n → ℝ≥0) :
    timeDerivative hB L hL hgen ((isSmoothBounded_cylinder L hL f hf hb hb' t).mderivLp P) =
      ∑ i, tensor (intervalIndicator (t i)) (cylinderPartial L hL f hf hb' t i) := by sorry
