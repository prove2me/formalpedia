-- Prove2me | Theorems.Thm_LefebvreVariations_cfsg_few_prime_factors
-- name    : LefebvreVariations.cfsg_few_prime_factors
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T01:00:32.801875+00:00
-- url     : https://prove2.me/theorems/2487df6e-d179-446d-953d-82dd6cc2a77b
-- title:
--   Lefebvre's variations, No. 123 — on a theme by Gorenstein, Lyons and Solomon: finite simple groups whose order has at most four prime factors are cyclic of prime order or A5
-- statement:
--   Let $G$ be a finite simple group (non-trivial, with no normal subgroups other than $1$ and $G$), and suppose the order $|G|$ has at most four prime factors, counted with multiplicity. Then $G$ is cyclic of prime order or isomorphic to the alternating group $A_5$:
--   $$
--   |G|\ \text{has at most 4 prime factors (with multiplicity)}\ \Longrightarrow\ G\cong \mathbb Z/p\ \text{or}\ G\cong A_5 .
--   $$
--
--   This is a finite-group special case in the spirit of the classification of finite simple groups: the non-abelian simple groups whose order has at most five prime factors (with multiplicity) are $\mathrm{PSL}(2,p)$ for $p=5,7,11,13$, so only $A_5\cong\mathrm{PSL}(2,5)$ of order $60=2^2\cdot3\cdot5$ has at most four.
--
--   **Formalization Note** `G : Type u` with `[Group G] [Finite G] [IsSimpleGroup G]`. The statement is self-contained: it does not import the definitions of `Prove2meCFSG.classification` and restates the relevant list entries by hand, using `Multiplicative (ZMod p)` with `p.Prime` for the cyclic groups, and `alternatingGroup (Fin 5)` for $A_5$. `IsSimpleGroup` includes non-triviality, so the trivial group is excluded; the hypothesis is exactly the one in the Lean statement.
--
--   **Why this is a variation.** Related to Prove2meCFSG.classification (Open) in spirit only: the statement restates, by hand and without importing the parent's definitions, the entries of the classification list whose order has at most four prime factors (cyclic of prime order, or A_5). It is self-contained and is not a formal special case of the parent.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Classical result of Burnside, Frobenius and Hoelder (1890s): the non-abelian simple groups whose order has at most five prime factors are PSL(2,p), p = 5, 7, 11, 13 (as reported in secondary sources, e.g. arXiv:2209.06510; original papers not individually verified). Only PSL(2,5) = A_5 has at most four.

import Mathlib

universe u

namespace LefebvreVariations

/-- A finite simple group whose order has at most four prime factors (with multiplicity) is cyclic of prime order or A_5. Self-contained restatement (the parent's definitions are not imported).
-/
theorem cfsg_few_prime_factors (G : Type u) [Group G] [Finite G] [IsSimpleGroup G]
    (h : (Nat.primeFactorsList (Nat.card G)).length ≤ 4) :
    (∃ p : ℕ, p.Prime ∧ Nonempty (G ≃* Multiplicative (ZMod p))) ∨
      Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  sorry

end LefebvreVariations
