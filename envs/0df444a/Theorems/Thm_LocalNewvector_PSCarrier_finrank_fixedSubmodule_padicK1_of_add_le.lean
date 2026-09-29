-- Prove2me | Theorems.Thm_LocalNewvector_PSCarrier_finrank_fixedSubmodule_padicK1_of_add_le
-- name    : LocalNewvector.PSCarrier.finrank_fixedSubmodule_padicK1_of_add_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/d32cd701-254d-5881-b7ed-c898c008be9c
-- title:
--   Oldform dimension count for a principal series
-- statement:
--   Let $p$ be a prime and let $\mu_1,\mu_2 : \mathbb{Q}_p^\times \to \mathbb{C}^\times$ be monoid homomorphisms. Assume $n_1, n_2 \in \mathbb{N}$ are conductor exponents for them in the sense of [`LocalNewvector.HasCharConductor`](def/LocalNewvector_CharConductor.html#L92): $\mu_i$ is trivial on `higherUnits p`$\,n_i$, the set of units $u$ with $\|u\|=1$ and either $n_i=0$ or $\|u-1\| \le p^{-n_i}$, while for every $m < n_i$ some $u$ in `higherUnits p`$\,m$ has $\mu_i(u) \ne 1$. Let $m \in \mathbb{N}$ satisfy $n_1+n_2 \le m$. The assertion is that the space of vectors in [`LocalNewvector.PSCarrier p`](def/LocalNewvector_PrincipalSeriesCarrier.html#L173)$\,\mu_1\,\mu_2$ — the $\mathbb{C}$-module of locally constant $f : \mathrm{GL}_2(\mathbb{Q}_p) \to \mathbb{C}$ with $f(\,$`borelElem p`$\,a_1\,a_2\,x \cdot g) = \mu_1(a_1)\mu_2(a_2)\,$`halfModulus p`$\,a_1\,a_2 \cdot f(g)$ for all $a_1,a_2 \in \mathbb{Q}_p^\times$, $x \in \mathbb{Q}_p$, $g \in \mathrm{GL}_2(\mathbb{Q}_p)$ — fixed by every element of [`LocalNewvector.padicK1 p`](def/LocalNewvector_CongruenceSubgroupK1.html#L161)$\,m$, namely the image in $\mathrm{GL}_2(\mathbb{Q}_p)$ of those $y \in \mathrm{GL}_2(\mathbb{Z}_p)$ with $y_{10} \in (p^m)$ and $y_{11}-1 \in (p^m)$, has $\mathbb{C}$-dimension $m - (n_1+n_2) + 1$ (truncated subtraction, harmless under the hypothesis $n_1+n_2 \le m$).
--
--   This is Casselman's oldform dimension count for a principal series representation: above the conductor $n_1+n_2$ of $\mu_1\mu_2$-type data, each increase of the level by one adds exactly one dimension of $K_1(p^m)$-fixed vectors. It feeds the uniqueness-of-newvector statement [`LocalNewvector.PSCarrier.finrank_fixedSubmodule_padicK1`](thm.html#LocalNewvector.PSCarrier.finrank_fixedSubmodule_padicK1) and the construction of $K_1(p^m)$-fixed twists of an adelic lift of a cusp form in the principal series case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalNewvector_PSCarrier_finrank_fixedSubmodule_padicK1_of_add_le.lean

import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem LocalNewvector.PSCarrier.finrank_fixedSubmodule_padicK1_of_add_le (p : ℕ) [Fact p.Prime] {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {n₁ n₂ : ℕ} (h₁ : LocalNewvector.HasCharConductor p μ₁ n₁) (h₂ : LocalNewvector.HasCharConductor p μ₂ n₂)
    {m : ℕ} (hm : n₁ + n₂ ≤ m) :
    Module.finrank ℂ
      ↥(LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 p m) (LocalNewvector.PSCarrier p μ₁ μ₂))
        = m - (n₁ + n₂) + 1 := by sorry
