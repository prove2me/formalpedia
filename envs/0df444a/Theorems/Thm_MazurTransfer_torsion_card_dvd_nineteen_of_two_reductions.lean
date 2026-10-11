-- Prove2me | Theorems.Thm_MazurTransfer_torsion_card_dvd_nineteen_of_two_reductions
-- name    : MazurTransfer.torsion_card_dvd_nineteen_of_two_reductions
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T12:50:30.502827+00:00
-- url     : https://prove2.me/theorems/5bb2370b-47c3-4ae5-aa2b-2323d754edb4
-- title:
--   The torsion bound from two reductions of cardinality nineteen
-- statement:
--   Let $G$ be an abelian group and let $r_3:G\to A$ and $r_5:G\to B$ be group homomorphisms, where both target groups have cardinality $19$. Suppose the kernel of $r_3$ contains no nonidentity element killed by an integer coprime to $3$, and the kernel of $r_5$ contains no nonidentity element killed by an integer coprime to $5$. Then the cardinality of the full torsion subgroup of $G$ divides $19$. In particular the torsion subgroup is finite, and its order is either $1$ or $19$. No rank or finite-generation hypothesis is required. Applied to the actual rational Picard group, the two homomorphisms are supplied by reduction of one integral Picard family.
-- source:
--   MazurTheorem formalization: the group-theoretic consequence of the actual order-13 Picard mod-3/mod-5 reduction maps and their prime-to-residue-characteristic torsion kernels. Mathlib pin 0df444a360eaa60ab8c11dca51a86af692955474; kernel mechanism independently ported from official Anthropic FLT pin 6e837e75355538c7f80bab5b956861e86c4eacc2.

import Mathlib

theorem MazurTransfer.torsion_card_dvd_nineteen_of_two_reductions
    {G A B : Type*} [CommGroup G] [Group A] [Group B]
    (r3 : G →* A) (r5 : G →* B)
    (hA : Nat.card A = 19) (hB : Nat.card B = 19)
    (h3 : ∀ (m : ℕ), ¬ 3 ∣ m → ∀ x : G, x ^ m = 1 → r3 x = 1 → x = 1)
    (h5 : ∀ (m : ℕ), ¬ 5 ∣ m → ∀ x : G, x ^ m = 1 → r5 x = 1 → x = 1) :
    Nat.card (CommGroup.torsion G) ∣ 19 := by sorry
