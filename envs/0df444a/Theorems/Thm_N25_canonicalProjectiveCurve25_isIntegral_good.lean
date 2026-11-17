-- Prove2me | Theorems.Thm_N25_canonicalProjectiveCurve25_isIntegral_good
-- name    : N25.canonicalProjectiveCurve25_isIntegral_good
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:38:22.88576+00:00
-- url     : https://prove2.me/theorems/1d4a7ce2-25ed-4fda-a62d-460e61f6bac0
-- title:
--   The canonical projective curve is integral in characteristics $2$ and $3$
-- statement:
--   Let $p$ be a prime with $p=2$ or $p=3$, and let $K$ be a field of characteristic $p$. Then the canonical projective quadric-cubic curve over $K$ is integral: $$C_K\text{ is integral}.$$ This records the good-prime specialization used by the finite-field place machinery. Formalization note: the primality witness for $p$ is supplied explicitly.
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

theorem N25.canonicalProjectiveCurve25_isIntegral_good
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3) (K : Type u) [Field K] [CharP K p] :
    IsIntegral (CanonicalProjectiveCurve25 K) := by sorry
