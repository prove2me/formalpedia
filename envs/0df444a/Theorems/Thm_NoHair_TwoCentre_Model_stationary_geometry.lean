-- Prove2me | Theorems.Thm_NoHair_TwoCentre_Model_stationary_geometry
-- name    : NoHair.TwoCentre.Model.stationary_geometry
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T21:51:13.735844+00:00
-- url     : https://prove2.me/theorems/88e17b35-990e-49b3-afed-000cfea2f033
-- title:
--   Tensor regularity, staticity, and chart matching for the specified one-horizon model
-- statement:
--   For the explicitly defined advanced Cartesian metric, Faraday field, stationary flow, and orientation on $M=\{(v,X):|X|>3/4,\ X\ne3e_1\}$, prove the tensor and symmetry hypotheses used by the static electrovacuum milestone. In the original isotropic coordinates the pullbacks must be exactly $g=-U^{-2}dt^2+U^2dx^2$ and $F=d(U^{-1}dt)$.
--
--   The advanced coefficients and their determinant have already been checked on a uniform horizon collar. The task includes lifting these coefficient results to smooth tensors and the specified time-oriented flow on the open submanifold, and checking hypersurface orthogonality on the exterior. [Horizon coefficients](https://prove2.me/theorems/5112e9cb-e66c-4ba3-ba7a-01031f4af387)
-- source:
--   J. B. Hartle and S. W. Hawking, Solutions of the Einstein-Maxwell equations with many black holes, Commun. Math. Phys. 26 (1972), 87–101, §II, equations (2.1)–(2.13), https://doi.org/10.1007/BF01645696.

import Definitions.Def_NoHair_TwoCentreBlackHole
import Definitions.Def_NoHair_TwoCentreIsotropic

open NoHair NoHair.TwoCentre NoHair.TwoCentre.Model Set
open scoped ContDiff Manifold

theorem NoHair.TwoCentre.Model.stationary_geometry :
    IsLorentzian metric ∧ IsSmoothBilinField metric ∧ IsSmoothBilinField faraday ∧
    IsTwoForm faraday ∧ IsTimeOrientation metric orientation ∧ IsSymmetryFlow metric faraday flow ∧
    IsStaticOn metric flow outer ∧ ∀ y ∈ exterior,
      pullbackCoeffs metric Model.chart y = isotropicMetric y ∧
      pullbackCoeffs faraday Model.chart y = TwoCentre.field y := by
  sorry
