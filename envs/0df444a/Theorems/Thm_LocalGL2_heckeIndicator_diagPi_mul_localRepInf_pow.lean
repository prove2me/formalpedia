-- Prove2me | Theorems.Thm_LocalGL2_heckeIndicator_diagPi_mul_localRepInf_pow
-- name    : LocalGL2.heckeIndicator_diagPi_mul_localRepInf_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/92b9e4ec-cdea-5f9b-b850-300aa3de513d
-- title:
--   Hecke recursion T· T_varpiⁿ=T_varpiⁿ⁺¹+q T_(varpi,varpiⁿ) for n≥ 2
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K$, let $\varpi \in R$ be irreducible with nonzero image in $K$, and assume the residue ring $R/(\varpi)$ is finite; let $R_0$ be a commutative ring and $k$ a natural number. Write $U =$ `integralSubgroup R K` for the image of $\mathrm{GL}_2(R)$ in $G = \mathrm{GL}_2(K)$ under the entrywise map $R \to K$, write $\pi =$ `diagPi` for the invertible matrix $\mathrm{diag}(\varpi,1)$ over $K$, and $L =$ `localRepInf` for the product $w\,\pi\,w$, where $w$ is the image in $G$ of the Weyl matrix `weylR` over $R$. For $g \in G$ whose image of $U\{g\}$ in $G/U$ is finite, `heckeIndicator R₀ g` denotes the element of the Hecke algebra $H(G,U;R_0)$ given by the $R_0$-valued indicator function of the double coset $UgU$. The hypotheses $hk2$, $hk3$, $hSk$ assert exactly these finiteness conditions for $L^{k+2}$, $L^{k+3}$ and $\pi L^{k+2}$ (the one for $\pi$ is supplied by `finite_image_mul_diagPi`). The conclusion is the identity in $H(G,U;R_0)$ $$\mathbf 1_{U\pi U}\cdot \mathbf 1_{U L^{k+2} U} = \mathbf 1_{U L^{k+3} U} + \bigl(\#(R/(\varpi))\bigr)\cdot \mathbf 1_{U \pi L^{k+2} U},$$ the product being the convolution product of the Hecke algebra and the coefficient the image of $\mathrm{Nat.card}(R/(\varpi))$ in $R_0$ acting by scalar multiplication.
--
--   This is the standard recursion in the spherical Hecke algebra of $\mathrm{GL}_2$ over a local ring: multiplication by the degree-one operator $T = \mathbf 1_{U\,\mathrm{diag}(\varpi,1)\,U}$ on the double coset of $\mathrm{diag}(1,\varpi^{n})$ with $n = k+2 \ge 2$, where the coefficient of the central-twist term is $q = \#(R/(\varpi))$ rather than the $q+1$ occurring at $n = 1$. It is used in the computation of orbital and twisted orbital integrals as shadows of Hecke operators and in the construction of matching local Hecke algebra homomorphisms at inert primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalGL2_heckeIndicator_diagPi_mul_localRepInf_pow.lean

import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Pointwise
open LocalGL2 HeckePair

theorem LocalGL2.heckeIndicator_diagPi_mul_localRepInf_pow
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    {R₀ : Type*} [CommRing R₀] (k : ℕ)
    (hk2 : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {localRepInf ϖ hϖ0 ^ (k + 2)}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite)
    (hk3 : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {localRepInf ϖ hϖ0 ^ (k + 3)}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite)
    (hSk : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2)}) :
          Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite) :
    heckeIndicator R₀ (diagPi ϖ hϖ0) (finite_image_mul_diagPi ϖ hϖ0 hϖ)
        * heckeIndicator R₀ (localRepInf ϖ hϖ0 ^ (k + 2)) hk2
      = (heckeIndicator R₀ (localRepInf ϖ hϖ0 ^ (k + 3)) hk3 : HeckeAlgebra (integralSubgroup R K) R₀)
        + (Nat.card (R ⧸ Ideal.span {ϖ}) : R₀)
          • heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2)) hSk := by sorry
