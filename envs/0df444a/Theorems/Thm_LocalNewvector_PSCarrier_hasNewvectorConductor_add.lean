-- Prove2me | Theorems.Thm_LocalNewvector_PSCarrier_hasNewvectorConductor_add
-- name    : LocalNewvector.PSCarrier.hasNewvectorConductor_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/c864b4ad-ab58-5101-94d8-ea1947e0b44f
-- title:
--   Casselman's conductor formula for the principal series
-- statement:
--   Let $p$ be a natural number carrying the hypothesis that it is prime, let $\mu_1,\mu_2 : \mathbb{Q}_p^\times \to \mathbb{C}^\times$ be monoid homomorphisms, and let $n_1,n_2$ be natural numbers. For a natural number $n$ write $U_n$ for the set `higherUnits p n` of units $u$ of $\mathbb{Q}_p$ with $\|u\|=1$ and, when $n>0$, $\|u-1\|\le p^{-n}$ (so $U_0$ is the whole set of norm-one units). The hypotheses are that $\mu_i$ has character conductor exponent $n_i$ in the sense of `HasCharConductor`, i.e. $\mu_i$ is trivial on $U_{n_i}$ and, for every $m<n_i$, some $u\in U_m$ has $\mu_i(u)\neq 1$. The conclusion is that the principal series carrier `PSCarrier p μ₁ μ₂` — the space of locally constant functions $f : \mathrm{GL}_2(\mathbb{Q}_p)\to\mathbb{C}$ satisfying $f(b(a_1,a_2,x)g) = \mu_1(a_1)\mu_2(a_2)\,\delta^{1/2}(a_1,a_2)\,f(g)$ for all $a_1,a_2\in\mathbb{Q}_p^\times$, $x\in\mathbb{Q}_p$, $g\in\mathrm{GL}_2(\mathbb{Q}_p)$, where $b(a_1,a_2,x)$ is the Borel element `borelElem` and $\delta^{1/2}$ is `halfModulus` — has newvector conductor exponent $n_1+n_2$ for its $\mathrm{GL}_2(\mathbb{Q}_p)$-action: the subspace of vectors fixed by the congruence subgroup `padicK1 p (n₁ + n₂)` is nonzero, while for every $m<n_1+n_2$ the subspace fixed by `padicK1 p m` is zero.
--
--   This is Casselman's conductor formula $c(B(\mu_1,\mu_2)) = c(\mu_1)+c(\mu_2)$ for the principal series of $\mathrm{GL}_2(\mathbb{Q}_p)$, in the form asserting the existence and the level-minimality of a $K_1(p^{n_1+n_2})$-fixed vector. It feeds the computation of the dimension of the fixed subspaces, [`LocalNewvector.PSCarrier.finrank_fixedSubmodule_padicK1`](thm.html#LocalNewvector.PSCarrier.finrank_fixedSubmodule_padicK1), and the local analysis of newforms of conductor exponent two at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalNewvector_PSCarrier_hasNewvectorConductor_add.lean

import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem LocalNewvector.PSCarrier.hasNewvectorConductor_add (p : ℕ) [Fact p.Prime] {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {n₁ n₂ : ℕ} (h₁ : LocalNewvector.HasCharConductor p μ₁ n₁) (h₂ : LocalNewvector.HasCharConductor p μ₂ n₂) :
    LocalNewvector.HasNewvectorConductor p (LocalNewvector.PSCarrier p μ₁ μ₂) (n₁ + n₂) := by sorry
