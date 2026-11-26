-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_integral_sq_centeredGaussian
-- name    : Malliavin.BrownianIteratedConstruction.integral_sq_centeredGaussian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:10:32.910192+00:00
-- url     : https://prove2.me/theorems/4e3d8534-5e13-53c3-992e-22a81c676e04
-- title:
--   Brownian Iterated Construction: integral sq centered Gaussian
-- statement:
--   The second moment of a centered real Gaussian is its variance.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/GaussianHermite.lean#L63-L66
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/GaussianHermite.lean#L63-L66

import Definitions.Def_Malliavin_BrownianHermite
import Mathlib.Probability.Distributions.Gaussian.Real
import Definitions.Def_Malliavin_GaussianHermite
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction

theorem Malliavin.BrownianIteratedConstruction.integral_sq_centeredGaussian (variance : ℝ≥0) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 variance) = (variance : ℝ) := by sorry
