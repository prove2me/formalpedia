-- Prove2me | Theorems.Thm_N25_canonicalProjectiveCurve25_isReduced_of_coneDomain
-- name    : N25.canonicalProjectiveCurve25_isReduced_of_coneDomain
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:38:41.566614+00:00
-- url     : https://prove2.me/theorems/84ee90c7-d641-4066-bc35-4b74021ab7b4
-- title:
--   A domain homogeneous cone gives a reduced projective curve
-- statement:
--   Let $K$ be a field, let $R$ be the homogeneous coordinate ring of the canonical cone, and assume $R$ is an integral domain. Let $C_K=\operatorname{Proj}(R)$. Then $$C_K\text{ is reduced}.$$ This is the reducedness half of the integrality proof for the literal projective model.
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

theorem N25.canonicalProjectiveCurve25_isReduced_of_coneDomain [IsDomain (CanonicalConeRing25 K)] :
    AlgebraicGeometry.IsReduced (CanonicalProjectiveCurve25 K) := by sorry
