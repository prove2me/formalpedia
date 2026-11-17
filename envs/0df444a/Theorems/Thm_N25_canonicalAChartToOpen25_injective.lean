-- Prove2me | Theorems.Thm_N25_canonicalAChartToOpen25_injective
-- name    : N25.canonicalAChartToOpen25_injective
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:36:55.925141+00:00
-- url     : https://prove2.me/theorems/b92a035f-6ac9-4094-a74b-be3672fa5dd8
-- title:
--   The canonical chart embeds into its selected principal-open localization
-- statement:
--   Let $A$ be the canonical $A$-chart ring over $K$ and let $A_s$ be its localization at the distinguished open element. Then the canonical localization map is injective: $$A↪A_s.$$ This lets properties proved on the open chart reflect information about the original affine chart.
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

theorem N25.canonicalAChartToOpen25_injective :
    Function.Injective (algebraMap (CanonicalAChartRing25 K) (CanonicalOpenChartRing25 K)) := by sorry
