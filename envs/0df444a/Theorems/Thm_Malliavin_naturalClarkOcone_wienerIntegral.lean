-- Prove2me | Theorems.Thm_Malliavin_naturalClarkOcone_wienerIntegral
-- name    : Malliavin.naturalClarkOcone_wienerIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:37:23.449215+00:00
-- url     : https://prove2.me/theorems/31e24ad4-045a-51ee-9e9e-31784c831834
-- title:
--   Malliavin: natural Clark Ocone wiener Integral
-- statement:
--   **Unconditional Clark--Ocone on the first chaos.** The predictable projection of the
--   Malliavin derivative of a Wiener integral integrates back to that same Wiener integral under the
--   constructed natural-filtration Itô operator; no martingale-representation assumption is needed.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoDuality.lean#L74-L89
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoDuality.lean#L74-L89

import Definitions.Def_Malliavin_NaturalItoRange
import Definitions.Def_Malliavin_ClarkOconeExamples
import Definitions.Def_Malliavin_NaturalItoDuality
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

theorem Malliavin.naturalClarkOcone_wienerIntegral
    (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    wienerIntegral hB g = expectationL2 (wienerIntegral hB g) +
      naturalItoIntegral hB hsm hnat
        (predictableProjection 𝓅
          (timeDerivative hB L hL hgen
            (mderivClosure P (wienerIntegral hB g)))) := by sorry
