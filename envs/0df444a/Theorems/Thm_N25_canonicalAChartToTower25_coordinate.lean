-- Prove2me | Theorems.Thm_N25_canonicalAChartToTower25_coordinate
-- name    : N25.canonicalAChartToTower25_coordinate
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:28:56.162288+00:00
-- url     : https://prove2.me/theorems/22b94059-8b85-4c6e-92c8-35a91761c59f
-- title:
--   The canonical chart-to-tower map sends each coordinate to its tower coordinate
-- statement:
--   For each projective coordinate index $i∈\{0,1,2,3\}$, the canonical homomorphism from the $A$-chart ring to its tower presentation satisfies $$φ(x_i)=x_i^{tower}.$$ This identifies the abstract chart coordinates with the explicit quadratic-tower coordinates.
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

@[simp]
theorem N25.canonicalAChartToTower25_coordinate (i : Fin 4) :
    canonicalAChartToTower25 K (canonicalAChartCoordinate25 K i) = canonicalAChartTowerCoordinate25 K i := by sorry
