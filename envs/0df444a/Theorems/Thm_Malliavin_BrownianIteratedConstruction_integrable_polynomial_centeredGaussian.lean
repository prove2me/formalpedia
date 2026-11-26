-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_integrable_polynomial_centeredGaussian
-- name    : Malliavin.BrownianIteratedConstruction.integrable_polynomial_centeredGaussian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:07:25.809244+00:00
-- url     : https://prove2.me/theorems/9e3d8044-1432-4d57-b2df-589300f362cb
-- title:
--   Brownian Iterated Construction: integrable polynomial centered Gaussian
-- statement:
--   Every polynomial is integrable under a centered Gaussian law.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/GaussianHermite.lean#L76-L85
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/GaussianHermite.lean#L76-L85

import Definitions.Def_Malliavin_BrownianHermite
import Mathlib.Probability.Distributions.Gaussian.Real
import Definitions.Def_Malliavin_GaussianHermite
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction

theorem Malliavin.BrownianIteratedConstruction.integrable_polynomial_centeredGaussian (variance : ℝ≥0) (p : Polynomial ℝ) :
    Integrable (fun x : ℝ ↦ p.eval x) (gaussianReal 0 variance) := by sorry
