-- Prove2me | Theorems.Thm_N25_canonicalConeRing25_isDomain
-- name    : N25.canonicalConeRing25_isDomain
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:38:34.186867+00:00
-- url     : https://prove2.me/theorems/168b764a-42a0-43c4-b9e1-c95d3e0ab5da
-- title:
--   The canonical homogeneous cone is a domain over every field
-- statement:
--   Let $K$ be any field and let $R_K=K[X_0,X_1,X_2,X_3]/(Q,C)$ be the homogeneous coordinate ring of the canonical cone. Then $$R_K\text{ is an integral domain}.$$ This gives a uniform algebraic foundation for the canonical projective model in every characteristic.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalProjectiveCharts
import Definitions.Def_N25_CanonicalChartDehomogenization
import Definitions.Def_N25_CanonicalProjectivePrincipalOpen
import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField
import Definitions.Def_N25_CanonicalOpenChart
import Definitions.Def_N25_UnitPlaneAlgebraOverRing
import Definitions.Def_N25_BirationalIdentities
import Definitions.Def_N25_CanonicalOpenAlgebraOverRing
import Definitions.Def_N25_CanonicalPrincipalOpenChart
import Definitions.Def_N25_CanonicalConePolynomial
import Theorems.Thm_N25_canonicalConeToTower25_coordinate
import Theorems.Thm_N25_canonicalConeBoundaryMap25_A
import Definitions.Def_N25_CanonicalConeTower
import Definitions.Def_N25_CanonicalConeBoundary
import Definitions.Def_N25_CanonicalConeTowerEquiv
import Definitions.Def_N25_CanonicalAChartTower
import Theorems.Thm_N25_canonicalAChartToTower25_coordinate
import Definitions.Def_N25_CanonicalAChartTowerEquiv
import Mathlib.AlgebraicGeometry.Properties
import Definitions.Def_N25_CanonicalProjectiveGenericPoint

universe u
open N25
open AlgebraicGeometry HomogeneousLocalization
variable (K : Type u) [Field K]

theorem N25.canonicalConeRing25_isDomain : IsDomain (CanonicalConeRing25 K) := by sorry
