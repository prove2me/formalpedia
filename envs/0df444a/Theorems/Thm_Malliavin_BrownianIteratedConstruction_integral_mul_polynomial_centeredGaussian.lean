-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_integral_mul_polynomial_centeredGaussian
-- name    : Malliavin.BrownianIteratedConstruction.integral_mul_polynomial_centeredGaussian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:12:44.835813+00:00
-- url     : https://prove2.me/theorems/9157131c-d7af-4120-affb-876c45d1d93f
-- title:
--   Brownian Iterated Construction: integral mul polynomial centered Gaussian
-- statement:
--   Gaussian integration by parts for real polynomials.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/GaussianHermite.lean#L88-L124
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/GaussianHermite.lean#L88-L124

import Definitions.Def_Malliavin_BrownianHermite
import Mathlib.Probability.Distributions.Gaussian.Real
import Definitions.Def_Malliavin_GaussianHermite
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction

theorem Malliavin.BrownianIteratedConstruction.integral_mul_polynomial_centeredGaussian (variance : ℝ≥0) (p : Polynomial ℝ) :
    (∫ x : ℝ, x * p.eval x ∂gaussianReal 0 variance) =
      (variance : ℝ) * ∫ x : ℝ, p.derivative.eval x ∂gaussianReal 0 variance := by sorry
