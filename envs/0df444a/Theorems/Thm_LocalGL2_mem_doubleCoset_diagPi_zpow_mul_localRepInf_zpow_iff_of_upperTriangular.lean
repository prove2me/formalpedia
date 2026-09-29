-- Prove2me | Theorems.Thm_LocalGL2_mem_doubleCoset_diagPi_zpow_mul_localRepInf_zpow_iff_of_upperTriangular
-- name    : LocalGL2.mem_doubleCoset_diagPi_zpow_mul_localRepInf_zpow_iff_of_upperTriangular
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/b7d5a63e-c373-5055-90d7-998599ee6e32
-- title:
--   Cartan cell of an upper-triangular element of GL₂(K)
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K$ (via a fixed algebra map $R \to K$ realising $K$ as the fraction field), let $\varpi \in R$ be irreducible and assume its image $\pi := \mathrm{algebraMap}\,\varpi$ in $K$ is nonzero. Let $g \in \mathrm{GL}_2(K)$, let $u_1, u_2 \in R^\times$ and $a, b \in \mathbb{Z}$, and suppose the underlying matrix of $g$ satisfies $g_{00} = u_1 \pi^{a}$, $g_{10} = 0$ and $g_{11} = u_2 \pi^{b}$ (so $g$ is upper triangular with unit-times-power-of-$\pi$ diagonal, the entry $g_{01}$ being arbitrary). Let $m \le n$ be integers. Write $U$ for `integralSubgroup R K`, the image of $\mathrm{GL}_2(R)$ in $\mathrm{GL}_2(K)$ under the entrywise map induced by $R \to K$, and let $t := \mathrm{diagPi}^{\,m} \cdot \mathrm{localRepInf}^{\,n}$, where $\mathrm{diagPi}$ is the diagonal element $\mathrm{diag}(\pi, 1)$ of $\mathrm{GL}_2(K)$ and $\mathrm{localRepInf}$ is $\mathrm{weylInt} \cdot \mathrm{diagPi} \cdot \mathrm{weylInt}$, with $\mathrm{weylInt}$ the image in $\mathrm{GL}_2(K)$ of the Weyl matrix `weylR` over $R$. Then the assertion $g \in U \cdot \{t\} \cdot U$ (the double coset as a subset of $\mathrm{GL}_2(K)$) is equivalent to the conjunction of: $m + n = a + b$; $m \le \min(a,b)$; $g_{01} = \pi^{m} r$ for some $r \in R$; and, in case $m < \min(a,b)$, there is no $r \in R$ with $g_{01} = \pi^{m+1} r$.
--
--   This identifies the Cartan cell (the pair of elementary divisors with respect to the maximal compact subgroup $\mathrm{GL}_2(R)$) of an upper-triangular element of $\mathrm{GL}_2(K)$: the double coset is determined by the valuation of the determinant together with $\min(a,b,v(g_{01}))$. It is used in the computation of orbital and weighted orbital integrals for Hecke operators on $\mathrm{GL}_2$, where the cells of the Cartan decomposition have to be recognised from explicit triangular representatives.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalGL2_mem_doubleCoset_diagPi_zpow_mul_localRepInf_zpow_iff_of_upperTriangular.lean

import Mathlib
import Definitions.Def_LocalLanglands_CartanDecomposition
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix LocalGL2 HeckePair

theorem LocalGL2.mem_doubleCoset_diagPi_zpow_mul_localRepInf_zpow_iff_of_upperTriangular
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) (hϖ0 : algebraMap R K ϖ ≠ 0)
    (g : GL (Fin 2) K) (u₁ u₂ : Rˣ) (a b : ℤ)
    (h00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = algebraMap R K u₁ * algebraMap R K ϖ ^ a)
    (h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = algebraMap R K u₂ * algebraMap R K ϖ ^ b)
    {m n : ℤ} (hmn : m ≤ n) :
    g ∈ doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0 ^ m * localRepInf ϖ hϖ0 ^ n) ↔
      m + n = a + b ∧ m ≤ min a b ∧
        (∃ r : R, (g : Matrix (Fin 2) (Fin 2) K) 0 1 = algebraMap R K ϖ ^ m * algebraMap R K r) ∧
        (m < min a b →
          ¬ ∃ r : R, (g : Matrix (Fin 2) (Fin 2) K) 0 1 = algebraMap R K ϖ ^ (m + 1) * algebraMap R K r) := by sorry
