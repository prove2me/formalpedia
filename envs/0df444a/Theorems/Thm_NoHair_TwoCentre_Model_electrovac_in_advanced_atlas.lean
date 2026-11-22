-- Prove2me | Theorems.Thm_NoHair_TwoCentre_Model_electrovac_in_advanced_atlas
-- name    : NoHair.TwoCentre.Model.electrovac_in_advanced_atlas
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T21:51:54.564048+00:00
-- url     : https://prove2.me/theorems/9c6e4313-c4c5-4c07-9904-f98092a7e763
-- title:
--   Transport and continuation of the two-centre field equations through the left horizon
-- statement:
--   Assume the coordinate Einstein–Maxwell equations on the entire punctured two-centre isotropic exterior. Prove that the regular advanced Cartesian metric and Faraday tensor satisfy the mission’s electrovacuum predicate at every point of the specified open spacetime, in every chart of its atlas.
--
--   On positive radius the two descriptions are related by a smooth coordinate and gauge transformation. On the horizon collar the coefficient identities extend analytically. The task includes the covariance or direct verification of the coordinate equation used in the mission. [Isotropic equations](https://prove2.me/theorems/4f53689b-31b8-4da5-8988-3877b29b410b) · [Horizon coefficients](https://prove2.me/theorems/5112e9cb-e66c-4ba3-ba7a-01031f4af387)
-- source:
--   J. B. Hartle and S. W. Hawking, Solutions of the Einstein-Maxwell equations with many black holes, Commun. Math. Phys. 26 (1972), 87–101, §II, equations (2.1)–(2.13), https://doi.org/10.1007/BF01645696.

import Definitions.Def_NoHair_TwoCentreBlackHole
import Definitions.Def_NoHair_TwoCentreIsotropic

open NoHair NoHair.TwoCentre NoHair.TwoCentre.Model Set
open scoped ContDiff Manifold

theorem NoHair.TwoCentre.Model.electrovac_in_advanced_atlas (h : ∀ y ∈ exterior, EinsteinMaxwellAt isotropicMetric TwoCentre.field y) :
    IsElectrovac metric faraday := by
  sorry
