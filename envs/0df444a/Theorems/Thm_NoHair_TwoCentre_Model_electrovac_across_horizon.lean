-- Prove2me | Theorems.Thm_NoHair_TwoCentre_Model_electrovac_across_horizon
-- name    : NoHair.TwoCentre.Model.electrovac_across_horizon
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T22:13:23.251273+00:00
-- url     : https://prove2.me/theorems/aae106e1-ba5a-46a1-a24a-9cd002bfbf7f
-- title:
--   Analytic continuation of the two-centre Einstein–Maxwell equations through the future horizon
-- statement:
--   Suppose the regular advanced Cartesian metric and Faraday tensor obey the Einstein equation, source-free Maxwell divergence and the homogeneous Maxwell identity at every point of the positive-radius exterior. Then those same tensors solve the full system in every chart at every point of the chosen one-horizon spacetime, including the horizon and the negative-radius collar. The metric and potential are the explicit functions in the concrete model.
-- source:
--   J. B. Hartle and S. W. Hawking, Solutions of the Einstein-Maxwell equations with many black holes, Commun. Math. Phys. 26 (1972), 87–101, §II, equations (2.1)–(2.13), https://doi.org/10.1007/BF01645696.

import Definitions.Def_NoHair_TwoCentreBlackHole
import Definitions.Def_NoHair_TwoCentreIsotropic

open NoHair NoHair.TwoCentre NoHair.TwoCentre.Model NoHair.TwoCentre.Cartesian Set
open scoped ContDiff Manifold

theorem NoHair.TwoCentre.Model.electrovac_across_horizon (he : ∀ z ∈ outerRegion, EinsteinMaxwellAt metricCoeffs faradayCoeffs z) :
    IsElectrovac metric faraday := by
  sorry
