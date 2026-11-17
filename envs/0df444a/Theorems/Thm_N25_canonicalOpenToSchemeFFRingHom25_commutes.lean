-- Prove2me | Theorems.Thm_N25_canonicalOpenToSchemeFFRingHom25_commutes
-- name    : N25.canonicalOpenToSchemeFFRingHom25_commutes
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:59.275213+00:00
-- url     : https://prove2.me/theorems/1890b180-45b1-43c7-ba46-f0412f8214f9
-- title:
--   The chart-to-function-field map preserves base-field constants
-- statement:
--   Let $K$ be a field, $A_K$ the canonical affine chart ring, and $K(C_K)$ the scheme function field. Let $ι_K:A_K→K(C_K)$ be the canonical chart-to-function-field ring homomorphism, and use the standard embeddings of $K$ into both rings. Then every $a∈K$ satisfies
--
--   $$ι_K(a)=a\quad\text{inside }K(C_K).$$
--
--   This records that the geometric germ map is a morphism over the coefficient field.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalSchemeFunctionField
import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField
import Definitions.Def_N25_CanonicalOpenChart
import Definitions.Def_N25_UnitPlaneAlgebraOverRing
import Definitions.Def_N25_BirationalIdentities
import Definitions.Def_N25_CanonicalOpenAlgebraOverRing
import Definitions.Def_N25_CanonicalProjectiveCharts
import Definitions.Def_N25_CanonicalChartDehomogenization
import Definitions.Def_N25_CanonicalProjectivePrincipalOpen
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
import Definitions.Def_N25_canonicalOpenToSchemeFFRingHom25

universe u
open N25
open AlgebraicGeometry CategoryTheory
variable (K : Type u) [Field K]
variable [IsIntegral (CanonicalProjectiveCurve25 K)]

theorem N25.canonicalOpenToSchemeFFRingHom25_commutes (a : K) :
    canonicalOpenToSchemeFFRingHom25 K (algebraMap K (CanonicalOpenChartRing25 K) a) =
      algebraMap K (CanonicalSchemeFF25 K) a := by sorry
