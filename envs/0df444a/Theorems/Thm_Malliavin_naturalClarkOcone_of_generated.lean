-- Prove2me | Theorems.Thm_Malliavin_naturalClarkOcone_of_generated
-- name    : Malliavin.naturalClarkOcone_of_generated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:48:29.049261+00:00
-- url     : https://prove2.me/theorems/f897ca68-b986-54c7-98aa-bf7a950d08ec
-- title:
--   Malliavin: natural Clark Ocone of generated
-- statement:
--   **The Brownian Clark--Ocone formula** on a generated linear Wiener space:
--   `F = E[F] + ∫ E[Dₜ F | 𝓕ₜ] dBₜ` for every `F ∈ 𝔻₁,₂`, with the natural-filtration Itô integral
--   and the predictable projection of the Malliavin derivative.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianClarkOconeCapstone.lean#L73-L88
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianClarkOconeCapstone.lean#L73-L88

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

theorem Malliavin.naturalClarkOcone_of_generated
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm)
    (F : D12 P) :
    F.1 = expectationL2 F.1 + naturalItoIntegral hB hsm hnat
      (predictableProjection filtration
        (timeDerivative hB coordinate coordinate_apply generated
          (mderivD12 P F))) := by sorry
