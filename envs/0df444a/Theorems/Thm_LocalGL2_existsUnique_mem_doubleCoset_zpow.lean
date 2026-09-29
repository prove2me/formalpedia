-- Prove2me | Theorems.Thm_LocalGL2_existsUnique_mem_doubleCoset_zpow
-- name    : LocalGL2.existsUnique_mem_doubleCoset_zpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/01eaab25-96fa-5735-a908-d5bd86d3a1ee
-- title:
--   Cartan decomposition of GL₂(K) over a discrete valuation ring
-- statement:
--   Let $R$ be a commutative domain that is a discrete valuation ring, and let $K$ be a field equipped with an $R$-algebra structure making it the fraction field of $R$. Let $\varpi \in R$ be an element whose image $\varpi \in K$ is non-zero and which is irreducible in $R$, and let $g \in \mathrm{GL}_2(K)$. Write $U$ for the subgroup `integralSubgroup R K` of $\mathrm{GL}_2(K)$, namely the image (range) of the map $\mathrm{GL}_2(R) \to \mathrm{GL}_2(K)$ induced by $R \to K$; write $\pi =$ `diagPi` for the unit $\mathrm{diag}(\varpi,1)$ of $\mathrm{GL}_2(K)$, with explicit inverse $\mathrm{diag}(\varpi^{-1},1)$, and $\pi' =$ `localRepInf` for the product $w\,\pi\,w$, where $w$ is the image in $\mathrm{GL}_2(K)$ of the integral matrix `weylR`. The assertion is that there is exactly one pair $p = (p_1,p_2) \in \mathbb{Z} \times \mathbb{Z}$ such that $p_1 \le p_2$ and $g$ belongs to the double coset $U \cdot \{\pi^{p_1}\pi'^{p_2}\} \cdot U$ (the pointwise product of sets in $\mathrm{GL}_2(K)$). Integer powers are taken in the group $\mathrm{GL}_2(K)$, so negative exponents are allowed.
--
--   This is the Cartan (elementary divisor) decomposition for $\mathrm{GL}_2$ over a discrete valuation ring: $\mathrm{GL}_2(K)$ is the disjoint union of the double cosets $\mathrm{GL}_2(R)\,\mathrm{diag}(\varpi^{m},\varpi^{n})\,\mathrm{GL}_2(R)$ with $m \le n$ in $\mathbb{Z}$, the normalisation $m \le n$ being what forces uniqueness, since conjugation by the Weyl element interchanges the two exponents. It indexes the local Hecke double cosets and is used in the computations of Hecke eigenfunctions and Satake combinations at a finite place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalGL2_existsUnique_mem_doubleCoset_zpow.lean

import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open LocalGL2 HeckePair

theorem LocalGL2.existsUnique_mem_doubleCoset_zpow
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ) (g : GL (Fin 2) K) :
    ∃! p : ℤ × ℤ, p.1 ≤ p.2 ∧
      g ∈ doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0 ^ p.1 * localRepInf ϖ hϖ0 ^ p.2) := by sorry
