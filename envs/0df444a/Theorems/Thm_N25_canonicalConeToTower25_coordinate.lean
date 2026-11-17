-- Prove2me | Theorems.Thm_N25_canonicalConeToTower25_coordinate
-- name    : N25.canonicalConeToTower25_coordinate
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:33:37.200732+00:00
-- url     : https://prove2.me/theorems/a40c1afc-e0e6-449d-81fe-a3d68dbbc20f
-- title:
--   The cone-to-tower equivalence preserves all four homogeneous coordinates
-- statement:
--   Let $K$ be a field, let $R$ be the canonical cone ring, and let $S$ be its equivalent two-step quadric-cubic tower presentation. For each coordinate index $i∈\{0,1,2,3\}$, the canonical map $e:R→S$ satisfies $$e(X_i)=X_i^{\mathrm{tower}}.$$ This pins the abstract ring equivalence to the literal projective coordinates.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Theorems.Thm_N25_canonicalConeBoundaryMap25_A
import Definitions.Def_N25_CanonicalConeTower
import Definitions.Def_N25_CanonicalConeBoundary
import Definitions.Def_N25_CanonicalProjectiveCharts
import Definitions.Def_N25_CanonicalChartDehomogenization
import Definitions.Def_N25_CanonicalProjectivePrincipalOpen
import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField
import Definitions.Def_N25_CanonicalOpenChart
import Definitions.Def_N25_UnitPlaneAlgebraOverRing
import Definitions.Def_N25_BirationalIdentities
import Definitions.Def_N25_CanonicalOpenAlgebraOverRing
import Definitions.Def_N25_CanonicalPrincipalOpenChart
import Definitions.Def_N25_CanonicalConeTowerEquiv

open N25
open Polynomial
variable (K : Type*) [Field K]

@[simp]
theorem N25.canonicalConeToTower25_coordinate (i : Fin 4) :
    canonicalConeToTower25 K (canonicalConeCoordinate25 K i) = canonicalConeTowerCoordinate25 K i := by sorry
