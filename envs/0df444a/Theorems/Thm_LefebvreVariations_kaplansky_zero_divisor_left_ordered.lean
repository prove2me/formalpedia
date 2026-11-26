-- Prove2me | Theorems.Thm_LefebvreVariations_kaplansky_zero_divisor_left_ordered
-- name    : LefebvreVariations.kaplansky_zero_divisor_left_ordered
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-25T23:44:44.21084+00:00
-- url     : https://prove2.me/theorems/ea7ce38e-28c5-4301-9ad4-2a5f7d1fb108
-- title:
--   Lefebvre's variations, No. 61 — on a theme by Kaplansky: the group algebra of a left-ordered group has no zero divisors
-- statement:
--   Let $K$ be a field and $G$ a group equipped with a linear order $\le$ that is left-invariant in the strict sense:
--   $$
--   \forall a,b,c\in G,\qquad a<b \;\Longrightarrow\; c\,a<c\,b .
--   $$
--   Assume also that $G$ is torsion-free (every element of finite order is $1$). Then the group algebra $K[G]$ has no zero divisors:
--   $$
--   \forall x,y\in K[G],\qquad xy=0 \;\Longrightarrow\; x=0 \ \text{ or } \ y=0 .
--   $$
--
--   This is the left-orderable case of Kaplansky's zero-divisor conjecture, which asserts the same for every torsion-free group and remains open in general. Left-orderable groups include free groups, torsion-free nilpotent groups and braid groups, and need not be abelian. A left-ordered group is automatically torsion-free, so the torsion-freeness hypothesis is redundant here; it is kept so that the statement has the same hypotheses as the parent plus the ordering.
--
--   **Formalization Note** The statement is `NoZeroDivisors (MonoidAlgebra K G)` for `K : Type` with `[Field K]` and `G : Type` with `[Group G] [LinearOrder G]`, under `hlt : ∀ a b c : G, a < b → c * a < c * b` and `hG : ∀ g : G, IsOfFinOrder g → g = 1`. The order is an arbitrary `LinearOrder` with no compatibility with the group beyond `hlt`. The hypothesis `hG` is not used in the proof (it follows from `hlt`); the conclusion is thus the parent `FCP.Kaplansky.zero_divisor_conjecture` for groups carrying such an order.
--
--   **Why this is a variation.** Variation on the open FCP.Kaplansky.zero_divisor_conjecture (K[G] has no zero divisors for G torsion-free). It adds a left-invariant linear order on G, a classical sufficient condition (it gives unique products), so it is a partial result of the parent for a large class of non-abelian groups.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Origin of this statement: the left-orderable case of Kaplansky's zero-divisor conjecture, platform problem FCP.Kaplansky.zero_divisor_conjecture (Open), with G assumed to carry a strict left-invariant linear order. The conjecture is attributed to Kaplansky; no page or theorem number is quoted here. The case is an elementary consequence of the definitions together with Mathlib: a group with a strictly left-monotone linear order has the unique-product property, and Mathlib proves that unique products over a domain give NoZeroDivisors for the monoid algebra. (Earlier drafts mentioned Higman 1940 and Passman 1977 ch. 13; those references were not verified and are deliberately omitted.)

import Mathlib

namespace LefebvreVariations

/-- Kaplansky's zero-divisor conjecture (`FCP.Kaplansky.zero_divisor_conjecture`), played for
**left-orderable** groups (possibly non-abelian, e.g. free groups, torsion-free nilpotent groups,
braid groups): if `G` carries a linear order with `a < b → c * a < c * b`, then `K[G]` has no zero
divisors, for every field `K`. Such a `G` is torsion-free, so the hypothesis `hG` of the parent
is automatic; it is kept to match the parent's own statement.
Source: classical (Higman, *The units of group-rings*, Proc. London Math. Soc. 46 (1940), treats
unique-product groups, which include the ordered ones; the statement for ordered groups is in
Passman, *The Algebraic Structure of Group Rings*, 1977, Ch. 13) -- cited from memory. -/
theorem kaplansky_zero_divisor_left_ordered (K : Type) [Field K] (G : Type) [Group G]
    [LinearOrder G] (hlt : ∀ a b c : G, a < b → c * a < c * b)
    (hG : ∀ g : G, IsOfFinOrder g → g = 1) : NoZeroDivisors (MonoidAlgebra K G) := by
  sorry

end LefebvreVariations
