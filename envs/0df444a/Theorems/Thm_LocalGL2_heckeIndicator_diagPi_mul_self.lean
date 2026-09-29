-- Prove2me | Theorems.Thm_LocalGL2_heckeIndicator_diagPi_mul_self
-- name    : LocalGL2.heckeIndicator_diagPi_mul_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/58a17fb3-33d3-5d5d-a78e-d24ca9e2cb74
-- title:
--   Square of the spherical Hecke operator at diag(varpi,1)
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K$ (a field equipped with an $R$-algebra structure making it the fraction field of $R$), let $\varpi \in R$ be irreducible whose image $\operatorname{algebraMap} R K\,\varpi$ in $K$ is non-zero, and assume the quotient $R/(\varpi)$ is finite; let $R_0$ be a commutative ring of coefficients. Write $U =$ `integralSubgroup R K`, the image of $\mathrm{GL}_2(R)$ in $\mathrm{GL}_2(K)$ under the entrywise map induced by $R \to K$, let `diagPi ϖ hϖ0` be the element $\mathrm{diag}(\varpi,1)$ of $\mathrm{GL}_2(K)$, and let `localRepInf ϖ hϖ0` be the product `weylInt R K * diagPi ϖ hϖ0 * weylInt R K`, where `weylInt R K` is the image in $\mathrm{GL}_2(K)$ of the matrix `weylR` over $R$. For $g \in \mathrm{GL}_2(K)$ whose coset set $U\{g\}$ has finite image in $\mathrm{GL}_2(K)/U$, `heckeIndicator R₀ g` denotes the element of the Hecke algebra `HeckeAlgebra (integralSubgroup R K) R₀` given by the $R_0$-valued indicator function of the double coset $UgU$. Assuming that the images of $U \cdot \{\,$`localRepInf ϖ hϖ0`$^2\}$ and of $U \cdot \{\,$`diagPi ϖ hϖ0` $\cdot$ `localRepInf ϖ hϖ0`$\}$ in $\mathrm{GL}_2(K)/U$ are finite, the theorem asserts the identity, in that Hecke algebra,
--   $$\mathbf 1_{U\,\mathrm{diag}(\varpi,1)\,U}\cdot \mathbf 1_{U\,\mathrm{diag}(\varpi,1)\,U} = \mathbf 1_{U\,(\mathrm{localRepInf})^2\,U} + \bigl(\,\#(R/(\varpi)) + 1\,\bigr)\cdot \mathbf 1_{U\,\mathrm{diag}(\varpi,1)\,(\mathrm{localRepInf})\,U},$$
--   where the finiteness of the image of $U\cdot\{\mathrm{diag}(\varpi,1)\}$ is provided by `finite_image_mul_diagPi ϖ hϖ0 hϖ`, and the cardinality of the residue ring, viewed in $R_0$, plus $1$ acts by scalar multiplication.
--
--   This is the first relation in the spherical Hecke algebra of $\mathrm{GL}_2$ over a discrete valuation ring, $T^2 = T_{\varpi^2} + (q+1)S$ with $q = \#(R/(\varpi))$, in the form where $T$ is the indicator of the double coset of $\mathrm{diag}(\varpi,1)$ and $S$ that of the central-type element $\mathrm{diag}(\varpi,1)\cdot$`localRepInf`. It is used in the construction of matching local Hecke operators at inert primes and in the identification of (twisted) orbital integrals with shadow expressions for elements with irreducible characteristic polynomial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalGL2_heckeIndicator_diagPi_mul_self.lean

import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Pointwise
open LocalGL2 HeckePair

theorem LocalGL2.heckeIndicator_diagPi_mul_self
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    {R₀ : Type*} [CommRing R₀]
    (h2 : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {localRepInf ϖ hϖ0 ^ 2}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite)
    (hS : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {diagPi ϖ hϖ0 * localRepInf ϖ hϖ0}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite) :
    heckeIndicator R₀ (diagPi ϖ hϖ0) (finite_image_mul_diagPi ϖ hϖ0 hϖ)
        * heckeIndicator R₀ (diagPi ϖ hϖ0) (finite_image_mul_diagPi ϖ hϖ0 hϖ)
      = (heckeIndicator R₀ (localRepInf ϖ hϖ0 ^ 2) h2 : HeckeAlgebra (integralSubgroup R K) R₀)
        + ((Nat.card (R ⧸ Ideal.span {ϖ}) : R₀) + 1)
          • heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) hS := by sorry
