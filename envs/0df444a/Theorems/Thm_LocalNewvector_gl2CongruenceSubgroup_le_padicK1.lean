-- Prove2me | Theorems.Thm_LocalNewvector_gl2CongruenceSubgroup_le_padicK1
-- name    : LocalNewvector.gl2CongruenceSubgroup_le_padicK1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/16962709-7a9f-5822-8d2a-da28ffb5622d
-- title:
--   Principal congruence subgroup contained in K₁(pⁿ)
-- statement:
--   Let $p$ be a prime and let $n$ be a natural number. The group [`FLT.SmoothVectors.gl2CongruenceSubgroup p n`](def/RepTheory_GL2CongruenceSubgroup.html#L181) consists of those $g \in \mathrm{GL}_2(\mathbb{Q}_p)$ such that every entry of $g - 1$ has $p$-adic absolute value at most $p^{-n}$ and every entry of $g^{-1} - 1$ has $p$-adic absolute value at most $p^{-n}$. The group [`LocalNewvector.padicK1 p n`](def/LocalNewvector_CongruenceSubgroupK1.html#L161) is [`LocalNewvector.congruenceK1`](def/LocalNewvector_CongruenceSubgroupK1.html#L55) formed with the uniformiser $p \in \mathbb{Z}_p$ and exponent $n$: it consists of those $x \in \mathrm{GL}_2(\mathbb{Q}_p)$ for which there exists $y \in \mathrm{GL}_2(\mathbb{Z}_p)$ whose image under the entrywise map induced by $\mathbb{Z}_p \to \mathbb{Q}_p$ equals $x$ and whose entries satisfy $y_{10} \in (p^n)$ and $y_{11} - 1 \in (p^n)$ as ideals of $\mathbb{Z}_p$. The assertion is the inclusion of subgroups of $\mathrm{GL}_2(\mathbb{Q}_p)$, $$\mathrm{gl2CongruenceSubgroup}(p,n) \le K_1(p^n),$$ i.e. every element of the first group lies in the second. No condition is imposed on the entries $y_{00}$, $y_{01}$ beyond integrality.
--
--   This is the elementary inclusion of the principal congruence subgroup of level $p^n$ in the Casselman-style group $K_1(p^n)$ at $p$. It serves as the bridge between the principal-congruence filtration, along which finiteness of spaces of fixed vectors in a smooth representation is formulated, and the $K_1$-filtration used to define the conductor exponent of a newvector; it is cited in the local analysis of principal-series constituents and of newform-attached vectors, and the companion inclusion in $K_0(p^n)$ is deduced from it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalNewvector_gl2CongruenceSubgroup_le_padicK1.lean

import Definitions.Def_LocalNewvector_ConductorDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem LocalNewvector.gl2CongruenceSubgroup_le_padicK1 (p : ℕ) [Fact p.Prime] (n : ℕ) :
    FLT.SmoothVectors.gl2CongruenceSubgroup p n ≤ LocalNewvector.padicK1 p n := by sorry
