-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_integral_sq_sub_variance_sq_centeredGaussian
-- name    : Malliavin.BrownianIteratedConstruction.integral_sq_sub_variance_sq_centeredGaussian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:18:48.112554+00:00
-- url     : https://prove2.me/theorems/c56b91d2-070f-5bdf-85fa-c7d7a9865190
-- title:
--   Brownian Iterated Construction: integral sq sub variance sq centered Gaussian
-- statement:
--   The centered square of a centered Gaussian has second moment twice the squared variance.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/GaussianHermite.lean#L326-L340
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/GaussianHermite.lean#L326-L340

import Definitions.Def_Malliavin_BrownianHermite
import Mathlib.Probability.Distributions.Gaussian.Real
import Definitions.Def_Malliavin_GaussianHermite
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction

theorem Malliavin.BrownianIteratedConstruction.integral_sq_sub_variance_sq_centeredGaussian (variance : ℝ≥0) :
    (∫ x : ℝ, (x ^ 2 - (variance : ℝ)) ^ 2 ∂gaussianReal 0 variance) =
      2 * (variance : ℝ) ^ 2 := by sorry
