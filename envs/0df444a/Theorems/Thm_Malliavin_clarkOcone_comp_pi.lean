-- Prove2me | Theorems.Thm_Malliavin_clarkOcone_comp_pi
-- name    : Malliavin.clarkOcone_comp_pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:40:07.224545+00:00
-- url     : https://prove2.me/theorems/87210acf-a198-491e-af9a-2e18819660dd
-- title:
--   Malliavin: clark Ocone comp pi
-- statement:
--   **Clark--Ocone for `f (F₁, …, Fₙ)`, `Fᵢ ∈ 𝔻₁,₂` arbitrary**:
--   `f (F) = E[f (F)] + C.itoIntegral (Π (∑ᵢ ∂ᵢ f (F) Dₜ Fᵢ))`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L398-L419
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean#L398-L419

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

theorem Malliavin.clarkOcone_comp_pi {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) (F : Fin n → D12 P) :
    (D12.compPi P hf hK F : Lp ℝ 2 P) =
      expectationL2 (D12.compPi P hf hK F : Lp ℝ 2 P) +
        C.itoIntegral (predictableProjection 𝓕 (∑ i,
          boundedSMul (G := fun p : ℝ≥0 × W ↦ fderiv ℝ f (fun i ↦ (F i : Lp ℝ 2 P) p.2)
              (Pi.single i 1))
            (aestronglyMeasurable_comp_snd (ν := nonnegativeLebesgueMeasure)
              (memLp_fderiv_pi_comp hf hK (fun i ↦ (F i : Lp ℝ 2 P)) i).aestronglyMeasurable)
            (C := K) (fun _ ↦ abs_fderiv_pi_single_le hK _ i)
            (C.timeDerivative (mderivD12 P (F i))))) := by sorry
