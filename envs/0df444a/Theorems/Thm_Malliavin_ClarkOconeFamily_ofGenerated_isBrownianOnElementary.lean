-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_ofGenerated_isBrownianOnElementary
-- name    : Malliavin.ClarkOconeFamily.ofGenerated_isBrownianOnElementary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:48:48.513875+00:00
-- url     : https://prove2.me/theorems/21a7c1a0-b650-5100-81d3-d4739be64fe1
-- title:
--   Clark Ocone Family: of Generated is Brownian On Elementary
-- statement:
--   The generated-space family has the genuine Brownian value on elementary adapted
--   processes.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianClarkOconeCapstone.lean#L124-L136
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianClarkOconeCapstone.lean#L124-L136

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

theorem Malliavin.ClarkOconeFamily.ofGenerated_isBrownianOnElementary
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm) :
    (ClarkOconeFamily.ofGenerated
      hB coordinate coordinate_apply generated hsm hnat).IsBrownianOnElementary := by sorry
