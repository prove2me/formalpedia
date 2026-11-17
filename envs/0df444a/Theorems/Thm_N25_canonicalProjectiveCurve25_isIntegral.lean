-- Prove2me | Theorems.Thm_N25_canonicalProjectiveCurve25_isIntegral
-- name    : N25.canonicalProjectiveCurve25_isIntegral
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:38:40.317451+00:00
-- url     : https://prove2.me/theorems/17b5a500-63c3-4ebb-a432-89748d416887
-- title:
--   The canonical projective curve is integral over every field
-- statement:
--   Let $K$ be any field and let $C_K$ be the projective complete intersection defined by the canonical quadric and cubic. Then $$C_K\text{ is an integral scheme}.$$ This makes the canonical model a legitimate irreducible curve with a function field over every coefficient field.
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

theorem N25.canonicalProjectiveCurve25_isIntegral : IsIntegral (CanonicalProjectiveCurve25 K) := by sorry
