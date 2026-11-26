-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_inner_brownianPurePowerIntegral_of_ne
-- name    : Malliavin.BrownianIteratedConstruction.inner_brownianPurePowerIntegral_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:37.520902+00:00
-- url     : https://prove2.me/theorems/1066f5bb-d4f3-4c78-a0c6-028479ef066d
-- title:
--   Brownian Iterated Construction: inner brownian Pure Power Integral of ne
-- statement:
--   Pure-power multiple integrals of different orders are orthogonal.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerIntegral.lean#L87-L94
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerIntegral.lean#L87-L94

import Definitions.Def_Malliavin_IteratedKernelPurePower
import Definitions.Def_Malliavin_BrownianPolynomialHermite
import Definitions.Def_Malliavin_BrownianPurePowerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.BrownianIteratedConstruction.inner_brownianPurePowerIntegral_of_ne
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {m n : ℕ} (hmn : m ≠ n)
    (f g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    inner ℝ (brownianPurePowerIntegral hB m f)
      (brownianPurePowerIntegral hB n g) = 0 := by sorry
