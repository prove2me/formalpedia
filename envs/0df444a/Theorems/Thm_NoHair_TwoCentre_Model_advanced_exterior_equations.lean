-- Prove2me | Theorems.Thm_NoHair_TwoCentre_Model_advanced_exterior_equations
-- name    : NoHair.TwoCentre.Model.advanced_exterior_equations
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T22:13:50.684278+00:00
-- url     : https://prove2.me/theorems/6a21cfbc-d526-4b53-80c8-a7399ba9d3d6
-- title:
--   Exterior Einstein–Maxwell equations after the explicit advanced coordinate and gauge change
-- statement:
--   Start with the verified Einstein–Maxwell equations in the full isotropic two-centre exterior. Transport them to the advanced Cartesian coordinates at positive signed radius. The smooth map is $X=(1+r)(x-b_-)/r$ and $v=t+9r/4+3\log r-1/r$, where $r=|x-b_-|$. The regular potential differs from the transformed isotropic potential by a closed radial form. The equations in the conclusion are the coordinate identities evaluated at the positive-radius points of the advanced chart. Analytic continuation from that region to the horizon and interior is handled separately. [Verified isotropic equations](https://prove2.me/theorems/4f53689b-31b8-4da5-8988-3877b29b410b)
-- source:
--   J. B. Hartle and S. W. Hawking, Solutions of the Einstein-Maxwell equations with many black holes, Commun. Math. Phys. 26 (1972), 87–101, §II, equations (2.1)–(2.13), https://doi.org/10.1007/BF01645696.

import Definitions.Def_NoHair_TwoCentreBlackHole
import Definitions.Def_NoHair_TwoCentreIsotropic

open NoHair NoHair.TwoCentre NoHair.TwoCentre.Model NoHair.TwoCentre.Cartesian Set
open scoped ContDiff Manifold

theorem NoHair.TwoCentre.Model.advanced_exterior_equations (h : ∀ y ∈ exterior, EinsteinMaxwellAt isotropicMetric TwoCentre.field y) :
    ∀ z ∈ outerRegion, EinsteinMaxwellAt metricCoeffs faradayCoeffs z := by
  sorry
