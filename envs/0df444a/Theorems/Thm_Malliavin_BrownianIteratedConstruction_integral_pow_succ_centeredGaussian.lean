-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_integral_pow_succ_centeredGaussian
-- name    : Malliavin.BrownianIteratedConstruction.integral_pow_succ_centeredGaussian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:05:31.524687+00:00
-- url     : https://prove2.me/theorems/f0eefe82-1186-4ddf-aff4-2dd3249c77cc
-- title:
--   Brownian Iterated Construction: integral pow succ centered Gaussian
-- statement:
--   Centered Gaussian moments satisfy the Stein recurrence.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/GaussianHermite.lean#L24-L60
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/GaussianHermite.lean#L24-L60

import Definitions.Def_Malliavin_BrownianHermite
import Mathlib.Probability.Distributions.Gaussian.Real
import Definitions.Def_Malliavin_GaussianHermite
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction

theorem Malliavin.BrownianIteratedConstruction.integral_pow_succ_centeredGaussian (variance : ℝ≥0) (n : ℕ) :
    (∫ x : ℝ, x ^ (n + 1) ∂gaussianReal 0 variance) =
      (variance : ℝ) * n * ∫ x : ℝ, x ^ (n - 1) ∂gaussianReal 0 variance := by sorry
