-- Prove2me | Theorems.Thm_LocalNewvector_PSCarrier_finrank_fixedSubmodule_padicK1
-- name    : LocalNewvector.PSCarrier.finrank_fixedSubmodule_padicK1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/08775461-e716-5b50-afbb-da4cfacf1531
-- title:
--   Dimension of K₁(p^m)-fixed vectors in principal series
-- statement:
--   Let $p$ be a prime and let $\mu_1,\mu_2:\mathbb{Q}_p^\times\to\mathbb{C}^\times$ be group homomorphisms. Assume [`LocalNewvector.HasCharConductor p μ₁ n₁`](def/LocalNewvector_CharConductor.html#L92) and [`LocalNewvector.HasCharConductor p μ₂ n₂`](def/LocalNewvector_CharConductor.html#L92) for natural numbers $n_1,n_2$: writing $U_n$ for the set [`LocalNewvector.higherUnits p n`](def/LocalNewvector_CharConductor.html#L62) of units $u$ of $\mathbb{Q}_p$ with $\lVert u\rVert=1$ and, when $n\neq 0$, $\lVert u-1\rVert\le p^{-n}$, this says that $\mu_i$ is trivial on $U_{n_i}$ and that for every $m<n_i$ some $u\in U_m$ has $\mu_i(u)\neq 1$. Let $m$ be any natural number. Consider [`LocalNewvector.PSCarrier p μ₁ μ₂`](def/LocalNewvector_PrincipalSeriesCarrier.html#L173), the type underlying the $\mathbb{C}$-submodule of functions $f:\mathrm{GL}_2(\mathbb{Q}_p)\to\mathbb{C}$ that are locally constant and satisfy $f(\mathrm{borelElem}\,(a_1,a_2,x)\cdot g)=\mu_1(a_1)\mu_2(a_2)\cdot\mathrm{halfModulus}(a_1,a_2)\cdot f(g)$ for all $a_1,a_2\in\mathbb{Q}_p^\times$, $x\in\mathbb{Q}_p$ and $g$, where `borelElem` supplies the relevant upper-triangular element and `halfModulus` the normalising factor. Let [`LocalNewvector.padicK1 p m`](def/LocalNewvector_CongruenceSubgroupK1.html#L161) be the subgroup of $\mathrm{GL}_2(\mathbb{Q}_p)$ consisting of the images of those $y\in\mathrm{GL}_2(\mathbb{Z}_p)$ with $y_{10}\in(p^m)$ and $y_{11}-1\in(p^m)$, and let [`LocalNewvector.fixedSubmodule`](def/LocalNewvector_ConductorDatum.html#L11) denote the $\mathbb{C}$-submodule of vectors fixed by every element of that subgroup. The conclusion is that this fixed submodule has $\mathbb{C}$-dimension $m+1-(n_1+n_2)$, the subtraction being truncated subtraction of natural numbers, i.e. $\max(0,m-(n_1+n_2)+1)$.
--
--   This is the dimension formula for vectors in a principal series representation of $\mathrm{GL}_2(\mathbb{Q}_p)$ fixed by the congruence subgroup $K_1(p^m)$: the space vanishes below the level $n_1+n_2$, is one-dimensional at that level (the newvector), and grows by one dimension per further level. It is used in the local analysis of adelic lifts of newforms, for instance when exhibiting $K_1$-fixed vectors in twists and when detecting ramification of the characters attached to a principal series constituent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalNewvector_PSCarrier_finrank_fixedSubmodule_padicK1.lean

import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem LocalNewvector.PSCarrier.finrank_fixedSubmodule_padicK1 (p : ℕ) [Fact p.Prime] {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {n₁ n₂ : ℕ} (h₁ : LocalNewvector.HasCharConductor p μ₁ n₁) (h₂ : LocalNewvector.HasCharConductor p μ₂ n₂)
    (m : ℕ) :
    Module.finrank ℂ
      ↥(LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 p m) (LocalNewvector.PSCarrier p μ₁ μ₂))
        = m + 1 - (n₁ + n₂) := by sorry
