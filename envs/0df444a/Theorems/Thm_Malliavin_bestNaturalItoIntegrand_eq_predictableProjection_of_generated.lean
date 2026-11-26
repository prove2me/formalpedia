-- Prove2me | Theorems.Thm_Malliavin_bestNaturalItoIntegrand_eq_predictableProjection_of_generated
-- name    : Malliavin.bestNaturalItoIntegrand_eq_predictableProjection_of_generated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:48:41.952847+00:00
-- url     : https://prove2.me/theorems/c306a31b-8ef0-5146-bb07-bcef6cec95e4
-- title:
--   Malliavin: best Natural Ito Integrand eq predictable Projection of generated
-- statement:
--   On a generated linear Wiener space, the inverse-Itô integrand of every `𝔻₁,₂` functional
--   is the predictable projection of its Malliavin derivative.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianClarkOconeCapstone.lean#L53-L68
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianClarkOconeCapstone.lean#L53-L68

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

theorem Malliavin.bestNaturalItoIntegrand_eq_predictableProjection_of_generated
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm)
    (F : D12 P) :
    bestNaturalItoIntegrand hB hsm hnat (centeredPartL2 F.1) =
      predictableProjection filtration
        (timeDerivative hB coordinate coordinate_apply generated
          (mderivD12 P F)) := by sorry
