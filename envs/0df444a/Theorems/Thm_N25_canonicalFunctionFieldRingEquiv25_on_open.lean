-- Prove2me | Theorems.Thm_N25_canonicalFunctionFieldRingEquiv25_on_open
-- name    : N25.canonicalFunctionFieldRingEquiv25_on_open
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:48:05.488718+00:00
-- url     : https://prove2.me/theorems/9dc24b41-145d-4958-8d79-467d129500cf
-- title:
--   The function-field equivalence fixes the canonical open chart
-- statement:
--   Let $K$ be a field, let $A_K$ be the canonical affine chart ring, let $K(C_K)$ be the scheme function field of the canonical projective curve, and let $F_K$ be the explicit canonical function field. Write $ι_K:A_K→K(C_K)$ for the germ map, $j_K:A_K→F_K$ for the natural field embedding, and $Θ_K:K(C_K)≃F_K$ for the canonical ring equivalence. Then for every $r∈A_K$,
--
--   $$Θ_K(ι_K(r))=j_K(r).$$
--
--   This shows that the scheme-theoretic and explicit function fields agree on their common affine chart.
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
import Definitions.Def_N25_canonicalFunctionFieldRingEquiv25

universe u
open N25
open AlgebraicGeometry CategoryTheory
variable (K : Type u) [Field K]
variable [IsIntegral (CanonicalProjectiveCurve25 K)]

theorem N25.canonicalFunctionFieldRingEquiv25_on_open (r : CanonicalOpenChartRing25 K) :
    canonicalFunctionFieldRingEquiv25 K (canonicalOpenToSchemeFFRingHom25 K r) =
      algebraMap (CanonicalOpenChartRing25 K) (CanonicalFF25 K) r := by sorry
