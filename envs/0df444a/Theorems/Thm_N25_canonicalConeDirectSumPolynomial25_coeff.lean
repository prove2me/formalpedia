-- Prove2me | Theorems.Thm_N25_canonicalConeDirectSumPolynomial25_coeff
-- name    : N25.canonicalConeDirectSumPolynomial25_coeff
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:29:22.846976+00:00
-- url     : https://prove2.me/theorems/5ee859fd-516e-4ad9-aaaa-9ed83f570b65
-- title:
--   The polynomial encoding remembers every homogeneous cone component
-- statement:
--   Let $K$ be a field, let $R=\bigoplus_{n≥0}R_n$ be the graded homogeneous coordinate ring of the canonical cone, and let $x=(x_n)$ be an element of its external direct sum. Let $Φ(x)$ be the canonical polynomial encoding and let $φ_n:R_n→L$ be the degree-$n$ fraction-piece map into the localized coefficient ring. Then $$[T^n]Φ(x)=φ_n(x_n).$$ This coefficient identity lets injectivity be checked one homogeneous degree at a time.
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

theorem N25.canonicalConeDirectSumPolynomial25_coeff (x : ⨁ n, canonicalConePiece25 K n) (n : ℕ) :
    (canonicalConeDirectSumPolynomial25 K x).coeff n = canonicalConeFractionPiece25 K n (x n) := by sorry
