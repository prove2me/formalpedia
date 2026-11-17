-- Prove2me | Theorems.Thm_N25_canonicalConePolynomial25_injective
-- name    : N25.canonicalConePolynomial25_injective
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:29:43.069604+00:00
-- url     : https://prove2.me/theorems/8c6cc388-79a9-498c-b32f-5e1a1cc10bf2
-- title:
--   The full polynomial encoding of the canonical cone is injective
-- statement:
--   Let $K$ be a field and let $A$ be the distinguished degree-one cone coordinate. If $A$ is regular, then the canonical graded-ring map that encodes a cone element as a polynomial over the localized chart is injective: $$A\text{ regular }⇒Φ:R→L[T]\text{ injective}.$$ This embeds the homogeneous cone in a polynomial ring where domain arguments are available.
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

theorem N25.canonicalConePolynomial25_injective (ha : IsRegular (canonicalConeA25 K)) :
    Function.Injective (canonicalConePolynomial25 K) := by sorry
