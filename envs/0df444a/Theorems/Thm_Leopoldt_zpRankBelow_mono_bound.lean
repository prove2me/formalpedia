-- Prove2me | Theorems.Thm_Leopoldt_zpRankBelow_mono_bound
-- name    : Leopoldt.zpRankBelow_mono_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:41:24.226994+00:00
-- url     : https://prove2.me/theorems/5ae3eedf-4140-4ccc-a143-acbd9cc6e02f
-- title:
--   The bounded $\mathbb{Z}_p$-rank is monotone in the bound
-- statement:
--   Let $p$ be a prime, $G$ a commutative topological group and $H \le G$ a subgroup. Write $\operatorname{rk}_b(H)$ for the largest $n \le b$ such that $\mathbb{Z}_p^{\,n}$ admits a continuous injective homomorphism into $G$ with image in $H$ (`zpRankBelow p b H`).
--
--   If $b \le b'$ then
--   $$\operatorname{rk}_b(H) \le \operatorname{rk}_{b'}(H),$$
--   since the set over which the supremum is taken only grows with the bound.
-- source:
--   Mission definition file Def_LeopoldtDefect (definition of zpRankBelow), after P. Mihailescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, Section 1.1 (Notations and fundamental facts)

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem zpRankBelow_mono_bound (p : ℕ) [Fact p.Prime] {G : Type*} [CommGroup G]
    [TopologicalSpace G] {b b' : ℕ} (h : b ≤ b') (H : Subgroup G) :
    zpRankBelow p b H ≤ zpRankBelow p b' H := by sorry
end Leopoldt
