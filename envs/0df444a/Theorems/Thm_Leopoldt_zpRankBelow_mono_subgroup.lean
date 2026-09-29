-- Prove2me | Theorems.Thm_Leopoldt_zpRankBelow_mono_subgroup
-- name    : Leopoldt.zpRankBelow_mono_subgroup
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:41:12.846988+00:00
-- url     : https://prove2.me/theorems/9cf10ae9-94a5-40ef-99a7-9d83830b186e
-- title:
--   The bounded $\mathbb{Z}_p$-rank is monotone in the subgroup
-- statement:
--   Let $p$ be a prime and $G$ a commutative topological group. For a subgroup $H \le G$ and a bound $b \in \mathbb{N}$, let $\operatorname{rk}_b(H)$ denote the largest $n \le b$ such that there is a continuous injective homomorphism $\mathbb{Z}_p^{\,n} \to G$ with image inside $H$ (this is `zpRankBelow p b H` from the mission definition file).
--
--   If $H \le H'$ are subgroups of $G$, then
--   $$\operatorname{rk}_b(H) \le \operatorname{rk}_b(H').$$
--
--   Indeed every embedding of $\mathbb{Z}_p^{\,n}$ landing in $H$ also lands in $H'$.
-- source:
--   Mission definition file Def_LeopoldtDefect (definition of zpRankBelow), after P. Mihailescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, Section 1.1 (Notations and fundamental facts)

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem zpRankBelow_mono_subgroup (p : ℕ) [Fact p.Prime] {G : Type*} [CommGroup G]
    [TopologicalSpace G] (b : ℕ) {H H' : Subgroup G} (h : H ≤ H') :
    zpRankBelow p b H ≤ zpRankBelow p b H' := by sorry
end Leopoldt
