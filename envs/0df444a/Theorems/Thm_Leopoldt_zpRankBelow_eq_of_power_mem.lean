-- Prove2me | Theorems.Thm_Leopoldt_zpRankBelow_eq_of_power_mem
-- name    : Leopoldt.zpRankBelow_eq_of_power_mem
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T23:03:04.184641+00:00
-- url     : https://prove2.me/theorems/fdc9cc9c-27df-41d9-af7f-96ee1ae490a2
-- title:
--   Bounded $p$-adic rank is unchanged under power-saturated subgroup inclusion
-- statement:
--   Let $H'\subseteq H$ be subgroups of a commutative topological group, and suppose there is a nonzero integer $m$ such that every $m$th power of an element of $H$ belongs to $H'$. Then, for any fixed bound $b$, their bounded $p$-adic ranks agree:
--
--   $$
--   \operatorname{rank}_{p,\le b}(H')=\operatorname{rank}_{p,\le b}(H).
--   $$
--
--   In particular, the power condition is the key step in showing that passage to a subgroup of finite index preserves the free $p$-adic rank. The statement applies to the rank notion used for the closures of global units in the mission.
--
--   **Formalization Note** The source rank witnesses are continuous injections of $\mathbb Z_p^n$; multiplication by a nonzero integer on this source remains continuous and injective.
-- source:
--   Formal consequence of the bounded p-adic rank definition in Definitions.Def_LeopoldtDefect, which formalizes Preda Mihăilescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544v4, Section 1.1, p. 3 (p-adic rank of the closure of units). The power condition expresses the standard finite-index subgroup mechanism; compare Section 1.3, Remark 1.A, p. 5.

import Definitions.Def_LeopoldtDefect

namespace Leopoldt
theorem zpRankBelow_eq_of_power_mem (p : ℕ) [Fact p.Prime]
    {G : Type*} [CommGroup G] [TopologicalSpace G]
    (b : ℕ) {H H' : Subgroup G} (hsub : H' ≤ H)
    (m : ℕ) (hm : m ≠ 0) (hpow : ∀ x ∈ H, x ^ m ∈ H') :
    zpRankBelow p b H' = zpRankBelow p b H := by sorry
end Leopoldt
