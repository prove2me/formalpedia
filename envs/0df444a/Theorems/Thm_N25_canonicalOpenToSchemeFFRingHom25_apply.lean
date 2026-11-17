-- Prove2me | Theorems.Thm_N25_canonicalOpenToSchemeFFRingHom25_apply
-- name    : N25.canonicalOpenToSchemeFFRingHom25_apply
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:43.814573+00:00
-- url     : https://prove2.me/theorems/e174e598-8f85-4b57-a989-fd7b9c20a6df
-- title:
--   The open-chart map to the function field is the germ map
-- statement:
--   Let $K$ be a field, $C_K$ the canonical projective level-$25$ curve, $U_K$ its distinguished principal open, $A_K$ the affine chart ring, and $K(C_K)$ the scheme-theoretic function field. Let $α_K$ be the principal-open identification, $s_K$ the associated section map, and $g_{U_K}:Γ(U_K,𝒪_{C_K})→K(C_K)$ the generic-point germ. If $ι_K:A_K→K(C_K)$ is the canonical open-chart ring homomorphism, then for every $r∈A_K$,
--
--   $$ι_K(r)=g_{U_K}(s_K(α_K(r))).$$
--
--   This realizes the chart-to-function-field map by taking an actual section and then its germ. Formalization note: nonemptiness of $U_K$ is supplied as an inferred instance.
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
import Theorems.Thm_N25_canonicalProjPrincipalOpen25_nonempty

universe u
open N25
open AlgebraicGeometry CategoryTheory
variable (K : Type u) [Field K]
variable [IsIntegral (CanonicalProjectiveCurve25 K)]

theorem N25.canonicalOpenToSchemeFFRingHom25_apply (r : CanonicalOpenChartRing25 K) :
    letI := canonicalProjPrincipalOpen25_nonempty K
    canonicalOpenToSchemeFFRingHom25 K r =
      (CanonicalProjectiveCurve25 K).germToFunctionField (canonicalProjPrincipalOpen25 K)
        (Proj.awayToSection (canonicalConePiece25 K) (canonicalConePrincipalElement25 K)
          (canonicalPrincipalOpenAlgEquiv25 K r)) := by sorry
