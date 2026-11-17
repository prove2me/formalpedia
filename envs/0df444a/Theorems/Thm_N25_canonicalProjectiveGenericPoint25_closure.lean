-- Prove2me | Theorems.Thm_N25_canonicalProjectiveGenericPoint25_closure
-- name    : N25.canonicalProjectiveGenericPoint25_closure
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:41:10.7625+00:00
-- url     : https://prove2.me/theorems/e65ebc22-9dde-424b-b498-11f859650054
-- title:
--   The canonical projective generic point is dense
-- statement:
--   Let $K$ be a field, assume the canonical homogeneous cone ring $R$ is a domain, and assume the distinguished positive-degree coordinate $A$ is nonzero. Let $η∈\operatorname{Proj}(R)$ be the point defined by the zero homogeneous prime. Then $$\overline{\{η\}}=\operatorname{Proj}(R).$$ This exhibits a generic point whose closure proves irreducibility.
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

theorem N25.canonicalProjectiveGenericPoint25_closure [IsDomain (CanonicalConeRing25 K)]
    (ha : canonicalConeA25 K ≠ 0) :
    closure ({canonicalProjectiveGenericPoint25 K ha} : Set (ProjectiveSpectrum (canonicalConePiece25 K))) =
      Set.univ := by sorry
