-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_integral_varianceHermite_centeredGaussian
-- name    : Malliavin.BrownianIteratedConstruction.integral_varianceHermite_centeredGaussian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:11:22.191277+00:00
-- url     : https://prove2.me/theorems/7e505181-e9b9-458f-adba-307bc46e9bea
-- title:
--   Brownian Iterated Construction: integral variance Hermite centered Gaussian
-- statement:
--   Generalized Hermite polynomials of positive order are centered under their matching
--   centered Gaussian law.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/GaussianHermite.lean#L128-L155
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/GaussianHermite.lean#L128-L155

import Definitions.Def_Malliavin_BrownianHermite
import Mathlib.Probability.Distributions.Gaussian.Real
import Definitions.Def_Malliavin_GaussianHermite
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction

theorem Malliavin.BrownianIteratedConstruction.integral_varianceHermite_centeredGaussian (variance : ℝ≥0) (n : ℕ) :
    (∫ x : ℝ, (varianceHermite (variance : ℝ) n).eval x
      ∂gaussianReal 0 variance) = if n = 0 then 1 else 0 := by sorry
