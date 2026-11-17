-- Prove2me | Theorems.Thm_N25_canonicalAChartRing25_isDomain
-- name    : N25.canonicalAChartRing25_isDomain
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:36:50.687987+00:00
-- url     : https://prove2.me/theorems/a4306004-6f5f-47d4-bf58-6375fcd74146
-- title:
--   The canonical $A$-chart coordinate ring is an integral domain
-- statement:
--   Let $A_{chart,K}$ be the coordinate ring of the canonical affine $A$-chart over the coefficient field $K$. Then $$A_{chart,K}\text{ is an integral domain}.$$ This supplies a function field for the chart and underlies the canonical curve's integrality.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower
import Theorems.Thm_N25_canonicalAChartToTower25_coordinate
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
variable (K : Type*) [Field K]

theorem N25.canonicalAChartRing25_isDomain : IsDomain (CanonicalAChartRing25 K) := by sorry
