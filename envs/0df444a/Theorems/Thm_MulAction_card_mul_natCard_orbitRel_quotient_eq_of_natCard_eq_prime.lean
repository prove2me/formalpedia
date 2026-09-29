-- Prove2me | Theorems.Thm_MulAction_card_mul_natCard_orbitRel_quotient_eq_of_natCard_eq_prime
-- name    : MulAction.card_mul_natCard_orbitRel_quotient_eq_of_natCard_eq_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/066fb680-60a4-5e46-ac13-417af1e630b1
-- title:
--   Orbit count for an action of a group of prime order
-- statement:
--   Let $G$ be a group and $X$ a type carrying a multiplicative $G$-action, with both $G$ and $X$ finite, and let $p$ be a prime natural number such that the number of elements of $G$ equals $p$. The conclusion is the identity of natural numbers $$p \cdot \#\bigl(\mathrm{MulAction.orbitRel.Quotient}\ G\ X\bigr) \;=\; \#X + (p-1)\cdot \#\bigl(\mathrm{MulAction.fixedPoints}\ G\ X\bigr),$$ where each $\#$ denotes the natural-number cardinality of a finite type: the first of the quotient of $X$ by the orbit equivalence relation, i.e. of the set of $G$-orbits; the second of $X$ itself; the third of the subtype of those $x \in X$ with $g \bullet x = x$ for every $g \in G$. The subtraction $p-1$ is truncated subtraction in $\mathbb{N}$, which is harmless since $p \ge 2$. Equivalently, since every orbit has size $1$ or $p$ and the singleton orbits are exactly the points fixed by all of $G$, the number of orbits equals $\#X^G + (\#X - \#X^G)/p$.
--
--   This is Burnside's orbit-counting lemma specialised to a group of prime order, where the only possible orbit sizes are $1$ and $p$. It is used in the counting of elliptic points on modular curves, for instance in the double counts relating the number of moduli points with $j = 0$ to the Dedekind $\psi$ function and $\nu_3(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MulAction_card_mul_natCard_orbitRel_quotient_eq_of_natCard_eq_prime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem MulAction.card_mul_natCard_orbitRel_quotient_eq_of_natCard_eq_prime
    (G : Type*) {X : Type*} [Group G] [MulAction G X] [Finite G] [Finite X]
    {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p) :
    p * Nat.card (MulAction.orbitRel.Quotient G X)
      = Nat.card X + (p - 1) * Nat.card (MulAction.fixedPoints G X) := by sorry
