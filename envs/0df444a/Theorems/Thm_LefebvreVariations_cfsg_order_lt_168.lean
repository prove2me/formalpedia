-- Prove2me | Theorems.Thm_LefebvreVariations_cfsg_order_lt_168
-- name    : LefebvreVariations.cfsg_order_lt_168
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T01:00:04.808117+00:00
-- url     : https://prove2.me/theorems/1e1c6d2f-2ea1-4de4-a00b-d637622922bf
-- title:
--   Lefebvre's variations: finite simple groups of order below 168 are cyclic of prime order or the alternating group A5
-- statement:
--   Let $G$ be a finite simple group (non-trivial, with no normal subgroups other than $1$ and $G$), and suppose $|G|<168$. Then $G$ is cyclic of prime order or isomorphic to the alternating group $A_5$ on five letters:
--   $$
--   |G|<168\ \Longrightarrow\ G\cong \mathbb Z/p\ \text{for a prime }p\ \text{ or }\ G\cong A_5 .
--   $$
--
--   This is a finite-group special case in the spirit of the classification of finite simple groups: the simple groups of small order are the cyclic groups of prime order and $A_5$ of order $60$; the next non-abelian simple group, $\mathrm{PSL}(2,7)$, has order $168$.
--
--   **Formalization Note** `G : Type u` with `[Group G] [Finite G] [IsSimpleGroup G]`. The statement is self-contained: it does not import the definitions of `Prove2meCFSG.classification` and restates the relevant list entries by hand, using `Multiplicative (ZMod p)` with `p.Prime` for the cyclic groups, and `alternatingGroup (Fin 5)` for $A_5$. `IsSimpleGroup` includes non-triviality, so the trivial group is excluded; the hypothesis is exactly the one in the Lean statement.
--
--   **Why this is a variation.** Related to Prove2meCFSG.classification (Open) in spirit only: the statement restates, by hand and without importing the parent's definitions, the entries of the classification list of order below 168 (cyclic of prime order, or A_5). It is self-contained and is not a formal special case of the parent; the parent remains open for all larger orders.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   O. Hoelder, "Die einfachen Gruppen im ersten und zweiten Hundert der Ordnungszahlen", Math. Ann. 40 (1892), 55-88 (verified: simple groups of order below 200); the orders 60 (A_5) and 168 (PSL(2,7)) were already known. Cited as the historical source; the statement itself is a standard fact.

import Mathlib

universe u

namespace LefebvreVariations

/-- Every finite simple group of order below 168 is cyclic of prime order or A_5 (order 60); the next non-abelian simple group is PSL(2,7) of order 168. Self-contained restatement (the parent's definitions are not imported).
-/
theorem cfsg_order_lt_168 (G : Type u) [Group G] [Finite G] [IsSimpleGroup G]
    (hlt : Nat.card G < 168) :
    (∃ p : ℕ, p.Prime ∧ Nonempty (G ≃* Multiplicative (ZMod p))) ∨
      Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  sorry

end LefebvreVariations
