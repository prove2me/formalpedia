-- Prove2me | Theorems.Thm_Malliavin_clarkOcone_mul_cylinder
-- name    : Malliavin.clarkOcone_mul_cylinder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:39:45.592391+00:00
-- url     : https://prove2.me/theorems/7886bdfb-5286-45f5-81c8-af9dfe582e18
-- title:
--   Malliavin: clark Ocone mul cylinder
-- statement:
--   **Clark--Ocone for `F · f (B t₁, …, B tₙ)`, `F ∈ 𝔻₁,₂` arbitrary**:
--   `F f (B) = E[F f (B)] + C.itoIntegral (Π (f (B) Dₜ F + F ∑ᵢ ∂ᵢ f (B) 1_{(0, tᵢ]}))`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L423-L455
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L423-L455

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_CylindricalGrowth
import Definitions.Def_Malliavin_ChainRule
import Definitions.Def_Malliavin_ClarkOconeExamples
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}

theorem Malliavin.clarkOcone_mul_cylinder {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hb : ∀ y, |f y| ≤ K) (hb' : ∃ K', ∀ y, ‖fderiv ℝ f y‖ ≤ K') (t : Fin n → ℝ≥0)
    {F : Lp ℝ 2 P} (hF : F ∈ domD12 P) :
    (memLp_mul_smoothBounded P
        (isSmoothBounded_cylinder C.coordinate C.coordinate_apply f hf ⟨K, hb⟩ hb' t) F).toLp _ =
      expectationL2 ((memLp_mul_smoothBounded P
        (isSmoothBounded_cylinder C.coordinate C.coordinate_apply f hf ⟨K, hb⟩ hb' t) F).toLp _)
        + C.itoIntegral (predictableProjection 𝓕
          (boundedSMul (G := fun p : ℝ≥0 × W ↦ f (fun i ↦ B (t i) p.2))
            (aestronglyMeasurable_comp_snd (ν := nonnegativeLebesgueMeasure)
              (isSmoothBounded_cylinder C.coordinate C.coordinate_apply f hf ⟨K, hb⟩ hb'
                t).continuous.aestronglyMeasurable)
            (C := K) (fun p ↦ hb (fun i ↦ B (t i) p.2))
            (C.timeDerivative (mderivD12 P ⟨F, hF⟩)) +
          ∑ i, tensor (intervalIndicator (t i))
            ((memLp_mul_cylinderPartial C.coordinate C.coordinate_apply f hf hb' t F i).toLp
              _))) := by sorry
