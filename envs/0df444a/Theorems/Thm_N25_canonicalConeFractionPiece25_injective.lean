-- Prove2me | Theorems.Thm_N25_canonicalConeFractionPiece25_injective
-- name    : N25.canonicalConeFractionPiece25_injective
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:29:36.763739+00:00
-- url     : https://prove2.me/theorems/ae2f1d08-0f88-47f2-819a-417c6868a241
-- title:
--   Regularity of the chart coordinate makes each homogeneous fraction map injective
-- statement:
--   Let $K$ be a field, let $R_n$ be the degree-$n$ piece of the canonical cone ring, and let $A∈R_1$ be the distinguished coordinate used for the $A$-chart. If multiplication by $A$ is injective in the cone ring, then for every $n≥0$ the canonical map $φ_n:R_n→L$ into the $A$-chart fraction ring is injective: $$A\text{ regular }⇒φ_n\text{ injective}.$$ This prevents a homogeneous coefficient from disappearing after localization.
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

theorem N25.canonicalConeFractionPiece25_injective (ha : IsRegular (canonicalConeA25 K)) (n : ℕ) :
    Function.Injective (canonicalConeFractionPiece25 K n) := by sorry
