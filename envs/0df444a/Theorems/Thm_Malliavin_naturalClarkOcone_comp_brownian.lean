-- Prove2me | Theorems.Thm_Malliavin_naturalClarkOcone_comp_brownian
-- name    : Malliavin.naturalClarkOcone_comp_brownian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:48:54.005655+00:00
-- url     : https://prove2.me/theorems/ea0c2995-a5a5-5cb2-9877-8238f27519b2
-- title:
--   Malliavin: natural Clark Ocone comp brownian
-- statement:
--   **Clark--Ocone for `g (B T)`** on a generated linear Wiener space, for `g` of class `C¹` with
--   exponential growth: `g (B T) = E[g (B T)] + ∫ Π (g' (B T) 1_{(0, T]}) dB` with the natural
--   Itô integral, where `Π` is the predictable projection.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianClarkOconeCapstone.lean#L173-L191
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianClarkOconeCapstone.lean#L173-L191

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

theorem Malliavin.naturalClarkOcone_comp_brownian
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {K c : ℝ} (hK : 0 ≤ K)
    (hc : 0 ≤ c) (hgb : ∀ x, |g x| ≤ K * Real.exp (c * |x|))
    (hgb' : ∀ x, |deriv g x| ≤ K * Real.exp (c * |x|)) (T : ℝ≥0) :
    (memLp_comp_brownian coordinate coordinate_apply hg hK hc hgb T).toLp _ =
      expectationL2 ((memLp_comp_brownian coordinate coordinate_apply hg hK hc hgb T).toLp _)
        + naturalItoIntegral hB hsm hnat (predictableProjection filtration
          (tensor (intervalIndicator T)
            ((memLp_deriv_comp_brownian coordinate coordinate_apply hg hK hc hgb' T).toLp
              _))) := by sorry
