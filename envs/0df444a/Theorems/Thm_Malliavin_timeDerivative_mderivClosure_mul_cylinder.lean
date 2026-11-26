-- Prove2me | Theorems.Thm_Malliavin_timeDerivative_mderivClosure_mul_cylinder
-- name    : Malliavin.timeDerivative_mderivClosure_mul_cylinder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:40:34.394309+00:00
-- url     : https://prove2.me/theorems/085abd6b-152c-41f6-b6d9-d161c2831603
-- title:
--   Malliavin: time Derivative mderiv Closure mul cylinder
-- statement:
--   **Time-form product rule with a cylindrical factor**:
--   `Dₜ (F · f (B t₁, …, B tₙ)) = f (B) Dₜ F + F ∑ᵢ ∂ᵢ f (B) 1_{(0, tᵢ]}(t)` for every `F ∈ 𝔻₁,₂`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L1005-L1062
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChainRule.lean#L1005-L1062

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

theorem Malliavin.timeDerivative_mderivClosure_mul_cylinder (hB : IsPreBrownianReal B P)
    (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) {C : ℝ} (hb : ∀ y, |f y| ≤ C)
    (hb' : ∃ C, ∀ y, ‖fderiv ℝ f y‖ ≤ C) (t : Fin n → ℝ≥0) {F : Lp ℝ 2 P} (hF : F ∈ domD12 P) :
    timeDerivative hB L hL hgen (mderivClosure P
        ((memLp_mul_smoothBounded P (isSmoothBounded_cylinder L hL f hf ⟨C, hb⟩ hb' t) F).toLp
          _)) =
      boundedSMul (G := fun p : ℝ≥0 × W ↦ f (fun i ↦ B (t i) p.2))
          (aestronglyMeasurable_comp_snd (ν := nonnegativeLebesgueMeasure)
            (isSmoothBounded_cylinder L hL f hf ⟨C, hb⟩ hb' t).continuous.aestronglyMeasurable)
          (fun _ ↦ hb _) (timeDerivative hB L hL hgen (mderivClosure P F)) +
        ∑ i, tensor (intervalIndicator (t i))
          ((memLp_mul_cylinderPartial L hL f hf hb' t F i).toLp _) := by sorry
