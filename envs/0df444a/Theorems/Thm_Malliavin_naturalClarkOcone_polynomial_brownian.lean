-- Prove2me | Theorems.Thm_Malliavin_naturalClarkOcone_polynomial_brownian
-- name    : Malliavin.naturalClarkOcone_polynomial_brownian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:49:26.694958+00:00
-- url     : https://prove2.me/theorems/4cf8d8db-d6e8-5fd0-8184-b2a1e69ed72d
-- title:
--   Malliavin: natural Clark Ocone polynomial brownian
-- statement:
--   **Clark--Ocone for polynomials of a Brownian coordinate** on a generated linear Wiener
--   space: `p (B T) = E[p (B T)] + ∫ Π (p' (B T) 1_{(0, T]}) dB` with the natural Itô integral.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianClarkOconeCapstone.lean#L195-L210
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianClarkOconeCapstone.lean#L195-L210

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

theorem Malliavin.naturalClarkOcone_polynomial_brownian
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm)
    (p : Polynomial ℝ) (T : ℝ≥0) :
    (memLp_polynomial_brownian coordinate coordinate_apply p T).toLp _ =
      expectationL2 ((memLp_polynomial_brownian coordinate coordinate_apply p T).toLp _)
        + naturalItoIntegral hB hsm hnat (predictableProjection filtration
          (tensor (intervalIndicator T)
            ((memLp_polynomial_derivative_brownian coordinate coordinate_apply p T).toLp
              _))) := by sorry
