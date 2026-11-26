-- Prove2me | Theorems.Thm_LefebvreVariations_cfsg_cyclic_sylow
-- name    : LefebvreVariations.cfsg_cyclic_sylow
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:59:44.110578+00:00
-- url     : https://prove2.me/theorems/1d8eec1d-0d8a-4059-b922-eab2f51d13c6
-- title:
--   Lefebvre's variations, No. 121 — on a theme by Gorenstein, Lyons and Solomon: a finite simple group whose Sylow subgroups are all cyclic is cyclic of prime order
-- statement:
--   Let $G$ be a finite simple group (non-trivial, with no normal subgroups other than $1$ and $G$), and suppose every Sylow subgroup of $G$ is cyclic. Then $G$ is cyclic of prime order:
--   $$
--   \text{all Sylow subgroups of }G\text{ are cyclic}\ \Longrightarrow\ G\cong \mathbb Z/p\ \text{for a prime }p .
--   $$
--
--   This is a finite-group consequence in the spirit of the classification of finite simple groups: a simple group all of whose Sylow subgroups are cyclic is of prime order. It follows from the classical structure theorem for such groups (they are metacyclic, hence solvable).
--
--   **Formalization Note** `G : Type u` with `[Group G] [Finite G] [IsSimpleGroup G]`. The statement is self-contained: it does not import the definitions of `Prove2meCFSG.classification` and restates the relevant list entries by hand, using `Multiplicative (ZMod p)` with `p.Prime` for the cyclic groups. `IsSimpleGroup` includes non-triviality, so the trivial group is excluded; the hypothesis is exactly the one in the Lean statement.
--
--   **Why this is a variation.** Related to Prove2meCFSG.classification (Open) in spirit only: the statement restates, by hand and without importing the parent's definitions, the slice of the classification list with all Sylow subgroups cyclic. It is self-contained and is not a formal special case of the parent.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Finite groups all of whose Sylow subgroups are cyclic (Z-groups) are metacyclic, hence solvable: classical, credited to Burnside (1905) and Zassenhaus (1935) in standard references such as the Wikipedia article on Z-groups (secondary source; exact original citations cited from memory, not verified). Combined with the elementary fact that a simple solvable group is cyclic of prime order.

import Mathlib

universe u

namespace LefebvreVariations

/-- A finite simple group all of whose Sylow subgroups are cyclic is cyclic of prime order (Hoelder, Burnside, Zassenhaus). Self-contained restatement (the parent's definitions are not imported).
-/
theorem cfsg_cyclic_sylow (G : Type u) [Group G] [Finite G] [IsSimpleGroup G]
    (hc : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G), IsCyclic P) :
    ∃ p : ℕ, p.Prime ∧ Nonempty (G ≃* Multiplicative (ZMod p)) := by
  sorry

end LefebvreVariations
