-- Prove2me | Theorems.Thm_Malliavin_naturalClarkOcone_condExp_of_generated
-- name    : Malliavin.naturalClarkOcone_condExp_of_generated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:48:39.445798+00:00
-- url     : https://prove2.me/theorems/d2a45d07-9df2-580d-a5ab-b1118f8d3292
-- title:
--   Malliavin: natural Clark Ocone cond Exp of generated
-- statement:
--   **The textbook Brownian Clark--Ocone theorem** on a generated linear Wiener space.  For every
--   `F ∈ 𝔻₁,₂`, the natural-filtration predictable projection of `Dₜ F` has a predictable
--   representative `G` whose time sections are `E[Dₜ F | 𝓕ₜ]` for almost every positive time, and
--   `F = E[F] + ∫ G dB` with the natural Itô integral.  No identity-family hypothesis remains.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianClarkOconeCapstone.lean#L142-L166
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianClarkOconeCapstone.lean#L142-L166

import Definitions.Def_Malliavin_BrownianHermiteClarkOcone
import Definitions.Def_Malliavin_BrownianPurePowerDuality
import Definitions.Def_Malliavin_ClarkOconeExamples
import Definitions.Def_Malliavin_NaturalFiltrationLeftContinuous
import Definitions.Def_Malliavin_BrownianClarkOconeCapstone
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
open BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

theorem Malliavin.naturalClarkOcone_condExp_of_generated
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm)
    (F : D12 P) :
    ∃ G : ℝ≥0 × W → ℝ,
      StronglyMeasurable[filtration.predictable] G ∧
      (predictableProjection filtration
          (timeDerivative hB coordinate coordinate_apply generated (mderivD12 P F)) :
            ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] G ∧
      (∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
        (fun w ↦ G (t, w)) =ᵐ[P]
          P[(fun w ↦ (timeDerivative hB coordinate coordinate_apply generated
            (mderivD12 P F)) (t, w)) | filtration t]) ∧
      F.1 = expectationL2 F.1 + naturalItoIntegral hB hsm hnat
        (predictableProjection filtration
          (timeDerivative hB coordinate coordinate_apply generated (mderivD12 P F))) := by sorry
