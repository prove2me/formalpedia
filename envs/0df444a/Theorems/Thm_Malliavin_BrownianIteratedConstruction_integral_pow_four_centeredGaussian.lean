-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_integral_pow_four_centeredGaussian
-- name    : Malliavin.BrownianIteratedConstruction.integral_pow_four_centeredGaussian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:18:43.063661+00:00
-- url     : https://prove2.me/theorems/aae72fa2-0f8c-5c08-84f4-b3a829351ac2
-- title:
--   Brownian Iterated Construction: integral pow four centered Gaussian
-- statement:
--   The fourth moment of a centered real Gaussian is three times the squared variance.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/GaussianHermite.lean#L69-L73
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/GaussianHermite.lean#L69-L73

import Definitions.Def_Malliavin_BrownianHermite
import Mathlib.Probability.Distributions.Gaussian.Real
import Definitions.Def_Malliavin_GaussianHermite
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction

theorem Malliavin.BrownianIteratedConstruction.integral_pow_four_centeredGaussian (variance : ℝ≥0) :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 variance) = 3 * (variance : ℝ) ^ 2 := by sorry
