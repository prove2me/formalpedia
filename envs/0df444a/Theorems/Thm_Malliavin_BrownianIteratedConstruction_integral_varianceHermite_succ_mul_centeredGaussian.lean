-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_integral_varianceHermite_succ_mul_centeredGaussian
-- name    : Malliavin.BrownianIteratedConstruction.integral_varianceHermite_succ_mul_centeredGaussian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:18:46.863339+00:00
-- url     : https://prove2.me/theorems/0d127477-29f9-58c3-b07b-e8de042fb397
-- title:
--   Brownian Iterated Construction: integral variance Hermite succ mul centered Gaussian
-- statement:
--   Raising one Hermite order transfers one order to the other factor in Gaussian inner
--   products.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/GaussianHermite.lean#L159-L294
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/GaussianHermite.lean#L159-L294

import Definitions.Def_Malliavin_BrownianHermite
import Mathlib.Probability.Distributions.Gaussian.Real
import Definitions.Def_Malliavin_GaussianHermite
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction

theorem Malliavin.BrownianIteratedConstruction.integral_varianceHermite_succ_mul_centeredGaussian
    (variance : ℝ≥0) (m n : ℕ) :
    (∫ x : ℝ, (varianceHermite (variance : ℝ) (m + 1)).eval x *
        (varianceHermite (variance : ℝ) n).eval x ∂gaussianReal 0 variance) =
      (variance : ℝ) * n *
        ∫ x : ℝ, (varianceHermite (variance : ℝ) m).eval x *
          (varianceHermite (variance : ℝ) (n - 1)).eval x
          ∂gaussianReal 0 variance := by sorry
