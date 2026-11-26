-- Prove2me | Theorems.Thm_Malliavin_mderivLp_cylinder
-- name    : Malliavin.mderivLp_cylinder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:20:19.42246+00:00
-- url     : https://prove2.me/theorems/26c356c1-11ad-4b25-9817-af24415b3275
-- title:
--   Malliavin: mderiv Lp cylinder
-- statement:
--   The Malliavin derivative of a cylindrical functional in `L²(P; H)`:
--   `D f(B t₁, …, B tₙ) = ∑ᵢ ∂ᵢ f (B) • ofDual (L tᵢ)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L562-L586
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L562-L586

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

theorem Malliavin.mderivLp_cylinder {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hb : ∃ C, ∀ y, |f y| ≤ C) (hb' : ∃ C, ∀ y, ‖fderiv ℝ f y‖ ≤ C) (t : Fin n → ℝ≥0) :
    (isSmoothBounded_cylinder L hL f hf hb hb' t).mderivLp P =
      ∑ i, smulLp (ofDual P (L (t i))) (cylinderPartial L hL f hf hb' t i) := by sorry
