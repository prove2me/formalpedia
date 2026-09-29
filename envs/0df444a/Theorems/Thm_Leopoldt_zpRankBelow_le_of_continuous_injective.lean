-- Prove2me | Theorems.Thm_Leopoldt_zpRankBelow_le_of_continuous_injective
-- name    : Leopoldt.zpRankBelow_le_of_continuous_injective
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T22:39:39.205081+00:00
-- url     : https://prove2.me/theorems/facfea05-d327-45c2-90cc-ff3be76e949b
-- title:
--   Functoriality of the bounded $p$-adic subgroup rank
-- statement:
--   Let $p$ be prime, and let $H$ and $H'$ be subgroups of commutative topological groups $G$ and $G'$. Suppose a continuous injective homomorphism $f:G\to G'$ carries $H$ into $H'$. For bounds $b\le b'$, the bounded $p$-adic ranks obey
--
--   $$
--   \operatorname{rank}_{p,\le b}(H)\le\operatorname{rank}_{p,\le b'}(H').
--   $$
--
--   Here the bounded rank is the largest $n$ within the stated bound for which a continuous injection of $\mathbb Z_p^n$ into the ambient group lands in the subgroup. This result packages the functorial principle used when unit closures are transported along field embeddings and other injective maps.
--
--   **Formalization Note** The topology and group structure on the targets are supplied as assumptions; the homomorphism is explicitly required to be continuous and injective.
-- source:
--   Formal consequence of the rank definition in LeopoldtDefect, based on Preda Mihăilescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544v4, Section 1.1, p. 3 (p-adic closure and rank), and Section 1.3, Remark 1.A, p. 5 (behavior of defects under embeddings in finite extensions).

import Definitions.Def_LeopoldtDefect

namespace Leopoldt
theorem zpRankBelow_le_of_continuous_injective (p : ℕ) [Fact p.Prime]
    {G G' : Type*} [CommGroup G] [TopologicalSpace G]
    [CommGroup G'] [TopologicalSpace G'] {b b' : ℕ}
    (f : G →* G') (hf : Function.Injective f) (hc : Continuous f)
    {H : Subgroup G} {H' : Subgroup G'}
    (hmap : ∀ g ∈ H, f g ∈ H') (hb : b ≤ b') :
    zpRankBelow p b H ≤ zpRankBelow p b' H' := by sorry
end Leopoldt
