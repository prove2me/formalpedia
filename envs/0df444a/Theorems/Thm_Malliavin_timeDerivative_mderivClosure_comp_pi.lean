-- Prove2me | Theorems.Thm_Malliavin_timeDerivative_mderivClosure_comp_pi
-- name    : Malliavin.timeDerivative_mderivClosure_comp_pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:40:19.775406+00:00
-- url     : https://prove2.me/theorems/e4cf28c9-1268-5a81-a1a8-f81bb356fa47
-- title:
--   Malliavin: time Derivative mderiv Closure comp pi
-- statement:
--   **The multivariate time-form chain rule**: `Dₜ f (F₁, …, Fₙ) = ∑ᵢ ∂ᵢ f (F) Dₜ Fᵢ` for
--   `F₁, …, Fₙ ∈ 𝔻₁,₂`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L1104-L1121
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L1104-L1121

import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_ChainRule
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
  {φ : ℝ → ℝ} {K : ℝ≥0}

theorem Malliavin.timeDerivative_mderivClosure_comp_pi (hB : IsPreBrownianReal B P)
    (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) {F : Fin n → Lp ℝ 2 P} (hF : ∀ i, F i ∈ domD12 P) :
    timeDerivative hB L hL hgen (mderivClosure P ((memLp_comp_pi P hf hK F).toLp _)) =
      ∑ i, boundedSMul (G := fun p : ℝ≥0 × W ↦ fderiv ℝ f (fun i ↦ F i p.2) (Pi.single i 1))
          (aestronglyMeasurable_comp_snd (ν := nonnegativeLebesgueMeasure)
            (memLp_fderiv_pi_comp hf hK F i).aestronglyMeasurable) (C := K)
        (fun _ ↦ abs_fderiv_pi_single_le hK _ i)
        (timeDerivative hB L hL hgen (mderivClosure P (F i))) := by sorry
