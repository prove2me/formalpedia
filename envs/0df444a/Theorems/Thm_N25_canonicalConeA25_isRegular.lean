-- Prove2me | Theorems.Thm_N25_canonicalConeA25_isRegular
-- name    : N25.canonicalConeA25_isRegular
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:36:48.70988+00:00
-- url     : https://prove2.me/theorems/940df573-1e86-4f24-9271-f52e35f11362
-- title:
--   The distinguished cone coordinate is a non-zero-divisor
-- statement:
--   Let $K$ be a field, let $R$ be the homogeneous coordinate ring of the canonical cone, and let $A∈R_1$ be the coordinate defining the selected affine chart. Then $$A\text{ is regular in }R.$$ This unlocks the localization and polynomial-embedding argument proving that the cone is a domain.
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

theorem N25.canonicalConeA25_isRegular : IsRegular (canonicalConeA25 K) := by sorry
