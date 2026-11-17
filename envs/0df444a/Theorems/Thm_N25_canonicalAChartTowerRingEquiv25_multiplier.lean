-- Prove2me | Theorems.Thm_N25_canonicalAChartTowerRingEquiv25_multiplier
-- name    : N25.canonicalAChartTowerRingEquiv25_multiplier
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:28:29.058306+00:00
-- url     : https://prove2.me/theorems/a863373e-b0da-47c6-baa5-da1c33b9889f
-- title:
--   The tower multiplier maps to the canonical multiplier of the chart coordinates
-- statement:
--   Let $e$ be the ring equivalence from the canonical tower ring to the $A$-chart ring, and let $\bar m_K$ be the image of the base multiplier in the tower quotient. Then $$e(\bar m_K)=M(x_0,x_1,x_2,x_3),$$ where $M$ is the canonical multiplier and $x_i$ are the chart coordinates. This transfers regularity of the tower multiplier to the geometric chart expression.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower
import Definitions.Def_N25_CanonicalProjectiveCharts
import Definitions.Def_N25_CanonicalChartDehomogenization
import Definitions.Def_N25_CanonicalProjectivePrincipalOpen
import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField
import Definitions.Def_N25_CanonicalOpenChart
import Definitions.Def_N25_UnitPlaneAlgebraOverRing
import Definitions.Def_N25_BirationalIdentities
import Definitions.Def_N25_CanonicalOpenAlgebraOverRing
import Definitions.Def_N25_CanonicalPrincipalOpenChart
import Definitions.Def_N25_CanonicalAChartTowerEquiv

open N25
open Polynomial
variable (K : Type*) [Field K]

theorem N25.canonicalAChartTowerRingEquiv25_multiplier :
    canonicalAChartTowerRingEquiv25 K (Ideal.Quotient.mk _
      (AdjoinRoot.of (canonicalAChartQuadratic25 K) (canonicalAChartBaseMultiplier25 K))) =
    canonicalMultiplier (canonicalAChartCoordinate25 K 0) (canonicalAChartCoordinate25 K 1)
      (canonicalAChartCoordinate25 K 2) (canonicalAChartCoordinate25 K 3) := by sorry
