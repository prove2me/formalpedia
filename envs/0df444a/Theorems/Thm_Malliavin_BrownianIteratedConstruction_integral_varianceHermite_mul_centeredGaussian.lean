-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_integral_varianceHermite_mul_centeredGaussian
-- name    : Malliavin.BrownianIteratedConstruction.integral_varianceHermite_mul_centeredGaussian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:11:20.624142+00:00
-- url     : https://prove2.me/theorems/0a169bb9-5183-5200-87ae-c8c231f10f2a
-- title:
--   Brownian Iterated Construction: integral variance Hermite mul centered Gaussian
-- statement:
--   Generalized Hermite polynomials are orthogonal under the centered Gaussian law with their
--   matching variance, with squared norm `n! variance^n`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/GaussianHermite.lean#L298-L323
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/GaussianHermite.lean#L298-L323

import Definitions.Def_Malliavin_BrownianHermite
import Mathlib.Probability.Distributions.Gaussian.Real
import Definitions.Def_Malliavin_GaussianHermite
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction

theorem Malliavin.BrownianIteratedConstruction.integral_varianceHermite_mul_centeredGaussian
    (variance : ℝ≥0) (m n : ℕ) :
    (∫ x : ℝ, (varianceHermite (variance : ℝ) m).eval x *
        (varianceHermite (variance : ℝ) n).eval x ∂gaussianReal 0 variance) =
      if m = n then m.factorial * (variance : ℝ) ^ m else 0 := by sorry
