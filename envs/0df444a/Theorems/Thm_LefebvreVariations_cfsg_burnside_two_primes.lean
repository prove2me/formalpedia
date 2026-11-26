-- Prove2me | Theorems.Thm_LefebvreVariations_cfsg_burnside_two_primes
-- name    : LefebvreVariations.cfsg_burnside_two_primes
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:59:26.545446+00:00
-- url     : https://prove2.me/theorems/0d0938da-548d-4e89-adec-5075d527c315
-- title:
--   Lefebvre's variations, No. 75 — on a theme by Gorenstein, Lyons and Solomon: a finite simple group of order p^a q^b is cyclic of prime order (Burnside)
-- statement:
--   Let $G$ be a finite simple group (non-trivial, with no normal subgroups other than $1$ and $G$), and suppose $|G|=p^a q^b$ for primes $p,q$ (not necessarily distinct) and integers $a,b\ge 0$. Then $G$ is cyclic of prime order:
--   $$
--   |G| = p^a q^b\ (p,q\text{ prime})\ \Longrightarrow\ G\cong \mathbb Z/r\ \text{for some prime }r .
--   $$
--
--   This is a finite-group consequence in the spirit of the classification of finite simple groups: for orders with at most two distinct prime divisors only the groups of prime order occur. It follows from Burnside's $p^aq^b$ theorem (such groups are solvable), granted that a simple solvable group has prime order.
--
--   **Formalization Note** `G : Type u` with `[Group G] [Finite G] [IsSimpleGroup G]`. The statement is self-contained: it does not import the definitions of `Prove2meCFSG.classification` and restates the relevant list entries by hand, using `Multiplicative (ZMod p)` with `p.Prime` for the cyclic groups. `IsSimpleGroup` includes non-triviality, so the trivial group is excluded; the hypothesis is exactly the one in the Lean statement.
--
--   **Why this is a variation.** Related to Prove2meCFSG.classification (Open) in spirit only: the statement restates, by hand and without importing the parent's definitions, the slice of the classification list for orders with at most two prime divisors. It is self-contained and is not a formal special case of the parent.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   W. Burnside, "On groups of order p^alpha q^beta", Proc. London Math. Soc. (2) 1 (1904), 388-392 (verified): every group of order p^a q^b is solvable. Combined with the elementary fact that a simple solvable group is cyclic of prime order.

import Mathlib

universe u

namespace LefebvreVariations

/-- Burnside's p^a q^b theorem in the shape of the classification list: a finite simple group of order p^a q^b is cyclic of prime order. Self-contained restatement (the parent's definitions are not imported).
-/
theorem cfsg_burnside_two_primes (G : Type u) [Group G] [Finite G] [IsSimpleGroup G]
    (p q a b : ℕ) [Fact p.Prime] [Fact q.Prime] (h : Nat.card G = p ^ a * q ^ b) :
    ∃ p : ℕ, p.Prime ∧ Nonempty (G ≃* Multiplicative (ZMod p)) := by
  sorry

end LefebvreVariations
