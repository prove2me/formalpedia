-- Prove2me | Theorems.Thm_N25_canonicalAChartOpenElement25_isRegular
-- name    : N25.canonicalAChartOpenElement25_isRegular
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:36:58.99919+00:00
-- url     : https://prove2.me/theorems/953a4953-4148-489d-b2b3-221c21282343
-- title:
--   The element defining the canonical affine principal open is a non-zero-divisor
-- statement:
--   Let $s$ be the distinguished element of the canonical $A$-chart ring whose powers define the selected principal open. Then $$\operatorname{Regular}(s).$$ This guarantees that localizing at $s$ is injective and preserves domainhood.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower
import Theorems.Thm_N25_canonicalAChartToTower25_coordinate
import Definitions.Def_N25_CanonicalProjectiveCharts
import Definitions.Def_N25_CanonicalChartDehomogenization
import Definitions.Def_N25_CanonicalProjectivePrincipalOpen
import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField
import Definitions.Def_N25_CanonicalOpenChart
import Definitions.Def_N25_UnitPlaneAlgebraOverRing
import Definitions.Def_N25_BirationalIdentities
import Definitions.Def_N25_CanonicalOpenAlgebraOverRing
import Definitions.Def_N25_CanonicalPrincipalOpenChart
import Definitions.Def_N25_CanonicalAChartTowerEquiv

open N25
variable (K : Type*) [Field K]

theorem N25.canonicalAChartOpenElement25_isRegular :
    IsRegular (canonicalAChartOpenElement25 K) := by sorry
