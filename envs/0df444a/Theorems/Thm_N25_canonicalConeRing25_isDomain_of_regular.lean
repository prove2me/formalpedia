-- Prove2me | Theorems.Thm_N25_canonicalConeRing25_isDomain_of_regular
-- name    : N25.canonicalConeRing25_isDomain_of_regular
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:29:48.654843+00:00
-- url     : https://prove2.me/theorems/e6bbdca2-6329-4152-a1d3-494b8afbf2c7
-- title:
--   A regular chart coordinate and a domain chart force the cone to be a domain
-- statement:
--   Let $K$ be a field, let $R$ be the homogeneous coordinate ring of the canonical cone, let $A∈R_1$ be the distinguished chart coordinate, and let $R_A^{(0)}$ be the associated degree-zero chart ring. Assume $A$ is regular in $R$ and $R_A^{(0)}$ is an integral domain. Then $$R\text{ is an integral domain}.$$ This transfers domainhood from the explicit affine chart to the full homogeneous cone.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

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

universe u
open N25
open HomogeneousLocalization DirectSum
variable (K : Type u) [Field K]

theorem N25.canonicalConeRing25_isDomain_of_regular
    (ha : IsRegular (canonicalConeA25 K)) [IsDomain (CanonicalAProjRing25 K)] :
    IsDomain (CanonicalConeRing25 K) := by sorry
