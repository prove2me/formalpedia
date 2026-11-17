-- Prove2me | Theorems.Thm_N25_canonicalAChartTowerRingEquiv25_coordinate
-- name    : N25.canonicalAChartTowerRingEquiv25_coordinate
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:46.356195+00:00
-- url     : https://prove2.me/theorems/2ee96027-cdea-4bca-8628-b9e6dc223f82
-- title:
--   The tower equivalence sends every tower coordinate back to the canonical chart coordinate
-- statement:
--   For each $i∈\{0,1,2,3\}$, let $e$ be the ring equivalence from the canonical tower presentation to the $A$-chart ring. Then $$e(x_i^{tower})=x_i.$$ This is the inverse coordinate formula for the tower presentation.
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

theorem N25.canonicalAChartTowerRingEquiv25_coordinate (i : Fin 4) :
    canonicalAChartTowerRingEquiv25 K (canonicalAChartTowerCoordinate25 K i) =
      canonicalAChartCoordinate25 K i := by sorry
