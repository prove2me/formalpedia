-- Prove2me | Theorems.Thm_LefebvreVariations_cfsg_odd_order
-- name    : LefebvreVariations.cfsg_odd_order
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:59:05.119743+00:00
-- url     : https://prove2.me/theorems/4fb2829a-2c36-4ae4-8aec-e802491aaa4f
-- title:
--   Lefebvre's variations, No. 117 — on a theme by Gorenstein, Lyons and Solomon: a finite simple group of odd order is cyclic of prime order (Feit and Thompson)
-- statement:
--   Let $G$ be a finite simple group (non-trivial, with no normal subgroups other than $1$ and $G$), and suppose $|G|$ is odd. Then $G$ is cyclic of prime order:
--   $$
--   |G|\ \text{odd}\ \Longrightarrow\ G\cong \mathbb Z/p\ \text{for some prime }p .
--   $$
--
--   This is a finite-group consequence in the spirit of the classification of finite simple groups: it is the part of that classification list that concerns odd order, where only the groups of prime order occur. It is equivalent to the Feit--Thompson odd order theorem (a finite group of odd order is solvable), granted that a simple solvable group has prime order.
--
--   **Formalization Note** `G : Type u` with `[Group G] [Finite G] [IsSimpleGroup G]`. The statement is self-contained: it does not import the definitions of `Prove2meCFSG.classification` and restates the relevant list entries by hand, using `Multiplicative (ZMod p)` with `p.Prime` for the cyclic groups. `IsSimpleGroup` includes non-triviality, so the trivial group is excluded; the hypothesis is exactly the one in the Lean statement.
--
--   **Why this is a variation.** Related to Prove2meCFSG.classification (Open) in spirit only: the statement restates, by hand and without importing the parent's definitions, the odd-order slice of the classification list (cyclic of prime order). It is self-contained and is not a formal special case of the parent.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   W. Feit and J. G. Thompson, "Solvability of groups of odd order", Pacific J. Math. 13 (1963), 775-1029 (verified): every finite group of odd order is solvable. Combined with the elementary fact that a simple solvable group is cyclic of prime order.

import Mathlib

universe u

namespace LefebvreVariations

/-- Feit-Thompson in the shape of the classification list: a finite simple group of odd order is cyclic of prime order. Self-contained restatement (the parent's definitions are not imported).
-/
theorem cfsg_odd_order (G : Type u) [Group G] [Finite G] [IsSimpleGroup G]
    (hodd : Odd (Nat.card G)) :
    ∃ p : ℕ, p.Prime ∧ Nonempty (G ≃* Multiplicative (ZMod p)) := by
  sorry

end LefebvreVariations
